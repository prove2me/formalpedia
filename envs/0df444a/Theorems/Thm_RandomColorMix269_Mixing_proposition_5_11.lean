-- Prove2me | Theorems.Thm_RandomColorMix269_Mixing_proposition_5_11
-- name    : RandomColorMix269.Mixing.proposition_5_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T21:04:45.961679+00:00
-- url     : https://prove2.me/theorems/b04ba71a-bb70-4227-9650-1e3f2f46fd06
-- title:
--   Proposition 5.11 — $|U|\ge e^{-d}n/2$ w.h.p., colourings of $G[U]$ extend, and $\nu$ is $q^{-(D+1)}$-marginally bounded
-- statement:
--   Fix $\eta\in(0,1)$; there is $d_0>1$ such that for every $d\ge d_0$, with $D=\lfloor(1+\eta/3)d\rfloor$, $S=N_G[V^{HD}]$ and $U=V\setminus S$:
--
--   1. with probability tending to $1$ over $G\sim G(n,d/n)$, $|U|\ge c_dn$ with $c_d=e^{-d}/2$;
--   2. for every integer $q\ge(1+\eta)d$, every $n$ and every graph $G$ on $[n]$ in which every component of $G[S]$ is a tree or unicyclic, $G$ is $q$-colourable, every proper colouring of $G[U]$ extends to a proper colouring of $G$, and the buffered marginal $\nu=(\mu_{G,q})_U$ is $b$-marginally bounded under all its feasible pinnings with
--   $$
--   b=q^{-(D+1)} .
--   $$
--
--   These are the hypotheses on $\nu$ needed to apply Theorem 5.7 and Lemma 5.6.
--
--   Differences from the source:
--   - encoding: vertex set [n] and colour set [q] → Fin n and Fin q; reason: relabelling only
--   - encoding: with probability at least 1 − o_n(1) over G ∼ G(n,d/n), for all sufficiently large n → the probability of the event under LPCommunity.SBMRecovery.erProb n (d/n) tends to 1; reason: the published law clamps d/n to [0,1], which differs from G(n,d/n) only for the finitely many n < d
--   - encoding: ν well defined (the proof shows G is q-colourable) → Colorable G q stated as a conclusion; reason: µ_{G,q} and ν exist only for colourable G
--   - encoding: the standing choice 'take d sufficiently large such that q − D ≥ 3, q ≥ 5 and D − 6 > d' (p.30) → ∃ d₀ > 1, ∀ d ≥ d₀; reason: the section's standing assumption on d
-- source:
--   Zhidan Li, Kuan Yang, STOC 2027 submission #269 (October 2026), PDF sha256 467638f1abc0f57df1bc0dcd9abfd308eb90ddbaf4947dac3eefa5f293ac6f05, pp.32–33, Proposition 5.11

import Definitions.Def_RandomColorMix269_Mixing_Parameters

open scoped Classical BigOperators
set_option autoImplicit false

namespace RandomColorMix269.Mixing

/-- Proposition 5.11, pp.32–33. The last clauses are deterministic under the
standing tree/unicyclic assumption; the linear-size clause is probabilistic. -/
theorem proposition_5_11 :
    ∀ η : ℝ, 0 < η → η < 1 → ∃ d₀ : ℝ, 1 < d₀ ∧ ∀ d : ℝ, d₀ ≤ d →
      WithHighProbability d (fun n G =>
        Real.exp (-d) / 2 * n ≤ ((lowRegion G (cutoff η d)).card : ℝ)) ∧
      ∀ q : ℕ, (1 + η) * d ≤ q → ∀ n : ℕ, ∀ G : SimpleGraph (Fin n),
        Pseudoforest G (buffer G (cutoff η d)) →
          Colorable G q ∧ ExtensionProperty G q (lowRegion G (cutoff η d)) ∧
            MarginalBounded (bufferedLaw G q (cutoff η d)) (marginalLower q (cutoff η d)) := by sorry

end RandomColorMix269.Mixing
