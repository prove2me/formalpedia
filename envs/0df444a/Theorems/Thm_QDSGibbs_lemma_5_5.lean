-- Prove2me | Theorems.Thm_QDSGibbs_lemma_5_5
-- name    : QDSGibbs.lemma_5_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:38:41.31384+00:00
-- url     : https://prove2.me/theorems/2d30e7b3-aa79-4d96-b650-18c4888d8813
-- title:
--   Lemma 5.5 — supports and bounds for the localized jump map
-- statement:
--   On a nearest-neighbour chain, with $M,\lambda$ as in Lemma 5.4 and $\mathcal T_{B,u}=\mathrm{Ad}_{O_{B,u}}\circ\mathcal R_B\circ\mathrm{Ad}_{O_{B,u}^{-1}}$, $S_{B,u}=\mathcal T_{B,u}^*(\mathbb 1)$: the map $\mathcal T_{B,u}$ is supported on $B^{\le u+1}$, $S_{B,u}$ is supported on $C_u(B)$,
--
--   $$
--   M^{-4}\mathbb 1\le S_B,\,S_{B,u}\le M^4\mathbb 1,\qquad \|\mathcal T_B\|_\diamond,\|\mathcal T_{B,u}\|_\diamond\le M^4,
--   $$
--
--   and
--
--   $$
--   \|\mathcal T_B-\mathcal T_{B,u}\|_\diamond+\|S_B-S_{B,u}\|\le C\beta J_{\mathrm{int}}e^{2\beta J_{\mathrm{int}}}e^{-\lambda u}.
--   $$
--
--   Differences from the source:
--   - reading: "universal constants" $c, C$ → constants chosen before the chain length, the local dimensions (any $d_i\ge2$), $\beta$ and the chain terms; reason: the paper's convention on p.39 ("$c, C$ denote universal positive constants")
--   - reading: constants ($C$, $c$, $C_d$) → constants required to be positive (and $c\le 1$ where $\lambda\le1$ is stipulated); reason: the paper's constants are positive by convention (p.39); a positive existential is the stronger reading
--   - encoding: sites $1,\dots,N$, bonds $W_i$ on $\{i,i+1\}$ → 0-based sites `Fin N`, bond `b : Fin (N−1)` on $\{b,b+1\}$; reason: a relabelling
--   - encoding: $O_B(u)$, the solution of (3.6) on $[0,1]$ → the solution on all of $\mathbb R$ chosen by `Classical.epsilon` (entrywise derivatives); reason: the linear ODE has continuous coefficients, so the global solution exists, is unique, and restricts to the paper's
--   - encoding: operators on a region $U$, partial traces $\mathrm{Tr}_S$, marginals and restricted Gibbs states acting on the subsystem → full-space matrices on $\prod_i \mathrm{Fin}\,d_i$: $A\otimes\mathbb 1$, `ptr S X` $=\mathbb 1_S\otimes\mathrm{Tr}_S X$, `gibbs β (hamOn I Ω)` $=\sigma^\Omega_\beta\otimes\mathbb 1/\dim$; reason: the paper extends operators by the identity in full-system expressions (p.10); norms, traces of products and covariances are unchanged
--   - encoding: real-valued $\|\cdot\|_{W_1}$, $D_\Psi(j)$, $\|\cdot\|_\diamond$ → values in $[0,\infty]$ (`ℝ≥0∞`); reason: the same values on the inputs the paper considers; an empty infimum or unbounded supremum gives $\infty$ instead of a junk $0$
-- source:
--   Rouzé–Stilck França, Rapid mixing of Gibbs samplers via quantum Dobrushin–Shlosman conditions, arXiv:2610.03578 (held file sha256 ede55815…), Lemma 5.5, p.42

import Mathlib
import Definitions.Def_QDSGibbs_chainGen

open scoped Matrix ENNReal ComplexOrder

namespace QDSGibbs

/-- **Lemma 5.5 (Bounds on the jump map)** (arXiv:2610.03578, held file sha256 ede55815…, Lemma 5.5,
p.42). The map `T_{B,u}` is supported on `B^{≤u+1}`, and `S_{B,u}` is supported on `C_u(B)`. With
`M, λ` from Lemma 5.4, `M^{−4} 1 ≤ S_B, S_{B,u} ≤ M^4 1` and `‖T_B‖⋄, ‖T_{B,u}‖⋄ ≤ M^4` (5.9).
Moreover `‖T_B − T_{B,u}‖⋄ + ‖S_B − S_{B,u}‖ ≤ CβJ_int e^{2βJ_int} e^{−λu}` (5.10).

**Formalization Note** `M = e^{βJ_int/2}`, `λ = c/(1 + βJ_int)` with universal `c ∈ (0, 1]` and
`C > 0` chosen before the chain; every interval `B`, every integer `u ≥ 0`. `T_B = jumpMap β I B
univ`, `T_{B,u} = jumpMap β I B (C_u(B))`, likewise `S`. Map support is `MapSupportedOn`; `≤` between
operators is the Loewner order; `‖·‖⋄` is `ℝ≥0∞`-valued. -/
theorem lemma_5_5 :
    ∃ c C : ℝ, 0 < c ∧ c ≤ 1 ∧ 0 < C ∧
      ∀ (N : ℕ), 1 ≤ N → ∀ (d : Fin N → ℕ), (∀ i, 2 ≤ d i) →
        ∀ (V : Fin N → Op d) (W : Fin (N - 1) → Op d), IsChainHam V W → ∀ β : ℝ, 0 < β →
          ∀ B : Finset (Fin N), IsInterval B → ∀ u : ℕ,
            MapSupportedOn (nbhd B ((u : ℝ) + 1)) (jumpMap β (chain V W) B (bdryNbhd B u)) ∧
            SupportedOn (bdryNbhd B u) (sOp β (chain V W) B (bdryNbhd B u)) ∧
            (sOp β (chain V W) B Finset.univ -
              (((Real.exp (β * jint (chain V W) / 2) ^ 4)⁻¹ : ℝ) : ℂ) • (1 : Op d)).PosSemidef ∧
            ((((Real.exp (β * jint (chain V W) / 2) ^ 4) : ℝ) : ℂ) • (1 : Op d) -
              sOp β (chain V W) B Finset.univ).PosSemidef ∧
            (sOp β (chain V W) B (bdryNbhd B u) -
              (((Real.exp (β * jint (chain V W) / 2) ^ 4)⁻¹ : ℝ) : ℂ) • (1 : Op d)).PosSemidef ∧
            ((((Real.exp (β * jint (chain V W) / 2) ^ 4) : ℝ) : ℂ) • (1 : Op d) -
              sOp β (chain V W) B (bdryNbhd B u)).PosSemidef ∧
            diamondNorm (jumpMap β (chain V W) B Finset.univ) ≤
              ENNReal.ofReal (Real.exp (β * jint (chain V W) / 2) ^ 4) ∧
            diamondNorm (jumpMap β (chain V W) B (bdryNbhd B u)) ≤
              ENNReal.ofReal (Real.exp (β * jint (chain V W) / 2) ^ 4) ∧
            diamondNorm (fun X => jumpMap β (chain V W) B Finset.univ X -
                jumpMap β (chain V W) B (bdryNbhd B u) X) +
              ENNReal.ofReal (opNorm (sOp β (chain V W) B Finset.univ -
                sOp β (chain V W) B (bdryNbhd B u))) ≤
              ENNReal.ofReal (C * β * jint (chain V W) * Real.exp (2 * β * jint (chain V W)) *
                Real.exp (-(c / (1 + β * jint (chain V W))) * u)) := by sorry

end QDSGibbs
