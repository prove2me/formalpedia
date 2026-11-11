-- Prove2me | Theorems.Thm_RandomColorMix269_Mixing_proposition_5_15
-- name    : RandomColorMix269.Mixing.proposition_5_15
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T21:04:29.543665+00:00
-- url     : https://prove2.me/theorems/a12fbdc4-7cf4-43c9-aa04-35472924596e
-- title:
--   Proposition 5.15 — w.h.p. $\mathrm{Ent}_\nu f\le C_{LD}\sum_{u\in U}\mathrm{Ent}^u_\nu f$ with $C_{LD}=2C_r\cdot4b^{-(3K\ln n+1)}\le n^B$, so $T_{\mathrm{rel}}(\mathcal L_\nu)\le n^B$
-- statement:
--   Fix $\eta\in(0,1)$; there is $d_0>1$ such that for every $d\ge d_0$ there are $C_{SI}>0$, $p\in(0,1)$ and $J\mapsto K_J$, depending only on $\eta,d$, such that $C_{SI}$ is the spectral-independence constant of Corollary 1.5 and $(p,K)$ satisfy Lemma 5.10, and for every integer $q\ge(1+\eta)d$ and every $J>2a+6$ (with $b,a,K=K_J$ as in §5.4) the exponent $B=a+3K\ln(1/b)+3$ is positive and, with probability tending to $1$ over $G\sim G(n,d/n)$: $G$ is $q$-colourable; $C_r=((N-R_0)/(r-R_0))^{R_0}>0$ is a valid factor in (10) for $\nu$ at block size $r=\lfloor p|U|/4\rfloor$, $N=|U|$, $R_0=\lceil4C_{SI}\ln n/b^2\rceil$; and for every observable $f\ge0$
--   $$
--   \mathrm{Ent}_\nu[f]\le C_{LD}\sum_{u\in U}\mathrm{Ent}^u_\nu(f),\qquad C_{LD}=2C_r\cdot4b^{-(3K\ln n+1)} .
--   $$
--   Consequently the continuous-time marginal Glauber dynamics $\mathcal L_\nu$ with rate one per vertex of $U$ has relaxation time at most $C_{LD}\le n^B$.
--
--   This converts logarithmic spectral independence into a polynomial relaxation bound for the buffered marginal.
--
--   Differences from the source:
--   - encoding: vertex set [n] and colour set [q] → Fin n and Fin q; reason: relabelling only
--   - encoding: statements about the uniform law µ_{G,q}, defined only when G has a proper q-colouring → the high-probability event also contains Colorable G q; reason: without it the zero mass function makes the pinned conditions vacuous; µ_{G,q} is meaningless otherwise
--   - encoding: with probability at least 1 − o_n(1) over G ∼ G(n,d/n), for all sufficiently large n → the probability of the event under LPCommunity.SBMRecovery.erProb n (d/n) tends to 1; reason: the published law clamps d/n to [0,1], which differs from G(n,d/n) only for the finitely many n < d
--   - encoding: spectral gap as an infimum over Var>0 and T_rel = 1/λ_gap with 1/0 = ∞ → infimum in ℝ≥0∞ (⊤ when no function has positive variance) and its inverse in ℝ≥0∞; reason: the source's convention; it avoids a real infimum of an empty set and a real inverse of 0
--   - generalization: C_SI the constant of Corollary 1.5, K = K_J of Lemma 5.14 for one fixed J > 2a + 6, C_r the factor of Theorem 5.7 → the conclusion also asserts that C_SI satisfies Corollary 1.5 and (p, K) satisfy Lemma 5.10, that the explicit C_r satisfies (10), and holds for every J > 2a + 6; reason: these pin down the source's constants; dropping the added conjuncts and fixing J gives the source's statement
--   - encoding: C_r the factor of Theorem 5.7 with C_r ≤ n^a → C_r equal to the explicit bound ((N−R₀)/(r−R₀))^{R₀} of Theorem 5.7; reason: the source's 'one can take'
-- source:
--   Zhidan Li, Kuan Yang, STOC 2027 submission #269 (October 2026), PDF sha256 467638f1abc0f57df1bc0dcd9abfd308eb90ddbaf4947dac3eefa5f293ac6f05, pp.34–35, Proposition 5.15 (constants from §5.4 p.33 and the proof p.35)

import Definitions.Def_RandomColorMix269_Mixing_Parameters

open scoped Classical BigOperators
set_option autoImplicit false

namespace RandomColorMix269.Mixing

/-- Proposition 5.15, pp.34–35. The SI and percolation constants are outputs,
chosen before q and n, not assumptions. Cr is the explicit valid upper
bound from Theorem 5.7. The exponent B is the one specified on p.35. -/
theorem proposition_5_15 :
    ∀ η : ℝ, 0 < η → η < 1 → ∃ d₀ : ℝ, 1 < d₀ ∧ ∀ d : ℝ, d₀ ≤ d →
      ∃ (Csi p : ℝ) (K : ℝ → ℝ), 0 < Csi ∧ PercolationConstants η d p K ∧
        ∀ q : ℕ, (1 + η) * d ≤ q →
          WithHighProbability d (fun n G => Colorable G q ∧
            SpectralIndependent (MarkovMixing.properColoringDist G q) (Csi * Real.log n)) ∧
          ∀ J : ℝ, 2 * exponentA Csi (marginalLower q (cutoff η d)) p + 6 < J →
            let b := marginalLower q (cutoff η d)
            let B := polynomialExponent Csi b p (K J)
            0 < B ∧ WithHighProbability d (fun n G =>
              let D := cutoff η d
              let ν := bufferedLaw G q D
              let N := (lowRegion G D).card
              let r := blockSize p N
              let Cr := chosenBlockFactor N Csi b p n
              let CLD := localEntropyConstant Cr b (K J) n
              Colorable G q ∧ 0 < Cr ∧ BlockFactorization ν r Cr ∧
                SingleFactorization ν CLD ∧ singleRelaxation ν ≤ ENNReal.ofReal CLD ∧
                  CLD ≤ (n : ℝ) ^ B) := by sorry

end RandomColorMix269.Mixing
