-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P47_theorem19_symmetricReduction
-- name    : QAlgorithms.Papers.Independent.Bridge50.P47.theorem19_symmetricReduction
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T08:51:31.43779+00:00
-- url     : https://prove2.me/theorems/605c76fa-e982-4ad2-8980-96fec498b29b
-- title:
--   Theorem 19: quantitative reduction to a symmetric channel
-- statement:
--   Let $\mathcal N$ be a finite type-I degradable channel with fixed dilations $U,V$ and a full-input-Schmidt-rank normalized test vector $\phi_0$, on a reference isomorphic to the input. Let $\mathcal M$ have the associated isometry $W:G'\to E\otimes E'$ of Lemma 18, obtained from the actual $AF$ support of $(I\otimes VU)\phi_0$, with either swap sign. Then $Q(\mathcal M)=0$, and a strong converse for $\mathcal M$ implies a strong converse for $\mathcal N$. Quantitatively, there exist $\mu\ge0$, $C>0$ and $n_0\ge2$, chosen before $\varepsilon,n$, such that for every $0\le\varepsilon<1$, with $\lambda=(1-\varepsilon)/5$, and every $n\ge n_0$,
--
--   $$
--   \log_2 N_E(n,\varepsilon\mid\mathcal N)\le nQ^{(1)}(\mathcal N)+\mu\sqrt{n\ln\frac{64n^{(\dim A)^2}}{\lambda^2}}+8\log_2\frac1\lambda+C\log_2 n+\log_2 N_E(n,1-\lambda\mid\mathcal M).
--   $$
--
--   Here $N_E$ denotes unassisted entanglement generation with purified error, and $Q^{(1)}$ is maximum coherent information. A strong converse means the optimal fixed-error limsup rate is at most the operational capacity for every error below one. The logarithmic remainder is eventual, avoiding an unjustified bound by $C\log_2 1$.
-- source:
--   "Pretty strong" converse for the quantum capacity of degradable channels, arXiv:1301.4927v3, PDF p. 11, Theorem 19: quantitative reduction to a symmetric channel

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P47

noncomputable section

open scoped BigOperators ComplexConjugate Matrix ComplexOrder

open Filter

namespace QAlgorithms.Papers.Independent.Bridge50.P47

open QAlgorithms.Papers.Independent.Information100

variable {A B E F R I O : Type*}

variable [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

variable [Fintype E] [DecidableEq E] [Fintype F] [DecidableEq F]

variable [Fintype R] [DecidableEq R] [Fintype I] [DecidableEq I]

variable [Fintype O] [DecidableEq O]

/-- Theorem 19, PDF pp.11–12: the companion is associated to phi0 as in
Lemma 18, not an unrelated symmetric channel. The O(log n) remainder is
quantified eventually, uniformly in epsilon; no bound by C log(1) is claimed. -/
theorem theorem19_symmetricReduction [Nonempty A] [Nonempty B] [Nonempty E]
    [Nonempty F] (U : Matrix (B × E) A ℂ) (V : Matrix (F × E) B ℂ)
    (negative : Bool) (hfactor : IsTypeIFactorization U V negative)
    (phi0 : EuclideanSpace ℂ (A × A)) (hphi0 : ‖phi0‖ = 1)
    (hfull : (traceRight (pureDensity phi0)).det ≠ 0)
    (W : Matrix (E × E) (Fin (supportDimension U V phi0)) ℂ)
    (hW : P67.IsIsometry W) (hassoc : Associated U V phi0 W)
    (hswap : P67.environmentSwap * W = swapSign negative • W) :
    P80.quantumCapacity (P67.receiverChannel W) = 0 ∧ (StrongConverse W → StrongConverse U) ∧
    ∃ mu C : ℝ, 0 ≤ mu ∧ 0 < C ∧ ∃ n0 : ℕ, 2 ≤ n0 ∧
      ∀ epsilon : ℝ, 0 ≤ epsilon → epsilon < 1 →
      let lambda := (1 - epsilon) / 5
      ∀ n ≥ n0,
        logNE U n epsilon ≤ (n : ℝ) * P67.maximumCoherentInformation U +
          mu * Real.sqrt ((n : ℝ) * Real.log
            (64 * (n : ℝ) ^ (Fintype.card A ^ 2) / lambda ^ 2)) +
          8 * Real.logb 2 (1 / lambda) + C * Real.logb 2 n +
          logNE W n (1 - lambda) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P47

end
