-- Prove2me | Theorems.Thm_QAlgorithms_Papers_BarnumKnill02_pgm_success_ge_one_sub_sum_bures
-- name    : QAlgorithms.Papers.BarnumKnill02.pgm_success_ge_one_sub_sum_bures
-- status  : Open
-- author  : @Goku
-- created : 2026-10-18T18:50:29.576843+00:00
-- url     : https://prove2.me/theorems/ce52a081-deb1-46cd-aca4-6b689928aa3c
-- title:
--   Barnum–Knill: the pretty good measurement succeeds with probability at least 1 − Σ_{i≠j} √(p_i p_j) F_BU(ρ̂_i, ρ̂_j)
-- statement:
--   Let $\{p_j, \hat\rho_j\}_{j \in O}$ be an ensemble of density matrices $\hat\rho_j$ on a finite-dimensional Hilbert space, indexed by a finite label set $O$, with probabilities $p_j \ge 0$, $\sum_j p_j = 1$. Write $\rho_j := p_j \hat\rho_j$ and $\rho_{\mathrm{out}} := \sum_j \rho_j$, and let $\rho_{\mathrm{out}}^{-1/2}$ be the generalized inverse square root (non-zero eigenvalues inverted, zero eigenvalues kept). The pretty good measurement (PGM) has effects $X_j = \rho_{\mathrm{out}}^{-1/2}\rho_j\rho_{\mathrm{out}}^{-1/2}$. For density matrices $\sigma_1,\sigma_2$ let $F_{BU}(\sigma_1,\sigma_2) := \operatorname{tr}\sqrt{\sigma_1^{1/2}\sigma_2\sigma_1^{1/2}}$ be the Bures–Uhlmann fidelity.
--
--   Then the success probability of the PGM, and therefore the optimal success probability $F_{\mathrm{cl}}$ over all measurements $\{M_j\}_{j\in O}$ (POVMs with one outcome per label), satisfy
--
--   $$
--   \sum_j \operatorname{tr}\big(\rho_{\mathrm{out}}^{-1/2}\rho_j\rho_{\mathrm{out}}^{-1/2}\rho_j\big) \;\ge\; 1-\sum_{i\ne j}\sqrt{p_ip_j}\,F_{BU}(\hat\rho_i,\hat\rho_j), \qquad F_{\mathrm{cl}} = \sup_{M}\sum_j p_j\operatorname{tr}(M_j\hat\rho_j) \;\ge\; 1-\sum_{i\ne j}\sqrt{p_ip_j}\,F_{BU}(\hat\rho_i,\hat\rho_j),
--   $$
--
--   the sums running over ordered pairs of distinct labels.
--
--   This bound expresses the error of state discrimination through pairwise overlaps only; it is the tool behind the polynomial query complexity of the hidden subgroup problem (Childs, Theorem 10.1).
--
--   **Formalization Note** The paper writes the left side of (39) as $F_{\mathrm{cl}}^2$ and opens (38) with $F_{\mathrm{cl}}^2 \ge F_{\mathrm{cl}}(\rho, R_{A,\rho}A)$, which is reversed relative to its own Corollary 4 and false in general (two equiprobable pure states with overlap 0.9). Its proof establishes the bound for the PGM success probability $F_{\mathrm{cl}}(\rho,R_{A,\rho}A)$ and then for the optimal $F_{\mathrm{cl}} \ge F_{\mathrm{cl}}(\rho,R_{A,\rho}A)$; that is what is stated. The reversal map of Eq. (35)–(36) is not formalized: for $A$ of form (35), classical fidelities of reversal are exactly measurement success probabilities on the ensemble.
-- source:
--   Reversing quantum dynamics with near-optimal quantum and classical fidelity (Barnum, Knill), arXiv:quant-ph/0004088v2, Theorem 5, PDF p. 11. https://arxiv.org/abs/quant-ph/0004088v2 . PDF SHA-256: 99ef00741dfeff7b21f88016555a72c10990bf1e616a8035178dd884a5ab7214.

import Definitions.Def_QAlgorithms_Defs_QuantumInformation
set_option autoImplicit false

namespace QAlgorithms.Papers.BarnumKnill02

/-- Barnum–Knill, Theorem 5 (p.11, Eq. (39), with Eq. (38) and the proof on pp.12–13).

For an ensemble `{p_j, ρ̂_j}` of density matrices with probabilities `p_j` (finitely many labels,
finite dimension), the success probability of the pretty good measurement,
`Σ_j tr(ρ_out^{-1/2} ρ_j ρ_out^{-1/2} ρ_j)` (`mixedPgmSuccess`), and hence the optimal success
probability over all measurements with outcome set the labels (`mixedOptSuccess`), are at least
`1 − Σ_{i ≠ j} √(p_i p_j) F_BU(ρ̂_i, ρ̂_j)`, where `F_BU(σ₁, σ₂) = tr √(σ₁^{1/2} σ₂ σ₁^{1/2})`
(`rootFidelity`).

The paper writes the left side of (39) as `F_cl^2`; its own proof bounds `F_cl(ρ, R_{A,ρ}A)` (the
PGM success probability) and then the optimal `F_cl ≥ F_cl(ρ, R_{A,ρ}A)`, which is what is stated
here (the squared form contradicts Corollary 4 and is false in general). -/
theorem pgm_success_ge_one_sub_sum_bures {O ι : Type*} [Fintype O] [DecidableEq O] [Fintype ι]
    [DecidableEq ι] (p : O → ℝ) (hp0 : ∀ j, 0 ≤ p j) (hp1 : ∑ j, p j = 1)
    (ρh : O → Matrix ι ι ℂ) (hρ : ∀ j, IsDensityMatrix (ρh j)) :
    1 - ∑ i, ∑ j ∈ Finset.univ.erase i, Real.sqrt (p i * p j) * rootFidelity (ρh i) (ρh j) ≤
        mixedPgmSuccess p ρh ∧
      1 - ∑ i, ∑ j ∈ Finset.univ.erase i, Real.sqrt (p i * p j) * rootFidelity (ρh i) (ρh j) ≤
        mixedOptSuccess p ρh := by
  sorry

end QAlgorithms.Papers.BarnumKnill02
