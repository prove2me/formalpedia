-- Prove2me | Theorems.Thm_SystemicHoldings_FEfficient_Supplement_theorem_4_2
-- name    : SystemicHoldings.FEfficient.Supplement.theorem_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T04:18:57.857916+00:00
-- url     : https://prove2.me/theorems/b1489c11-099f-4118-8c72-f0a05f899a72
-- title:
--   Theorem 4.2, p. 14 — full diversification $Q^{\mathrm{diversified}}$ is f-efficient iff $q$ and $z=G^{-1}\mathbf 1_K$ are linearly dependent
-- statement:
--   Consider $K$ assets and $N$ banks. Asset shocks have means $\mu\in\mathbb R^K$ and standard deviations $\sigma\in\mathbb R^K$ with $\sigma_k>0$ for every $k$ (Assumption 2), and
--   $$
--   G=\mu\mu^\top+\mathrm{Diag}(\sigma_1^2,\dots,\sigma_K^2)
--   $$
--   is the second-moment matrix of the shocks. Let $q\in\mathbb R^K$ be the total initial holdings, $b\in\mathbb R^N$ the banks' budgets, and $v\in\mathbb R^N$ the vector of bank weights (the network multipliers). Assume
--
--   1. $\sum_k q_k=\sum_i b_i=:T$ and $T\neq 0$;
--   2. Assumption 3: $v_i\neq v_j$ for some banks $i,j$, and $b^\top v\neq 0$.
--
--   The feasible set is $\mathscr D(q,b)=\{Q\in\mathbb R^{K\times N}: Q\mathbf 1_N=q,\ \mathbf 1_K^\top Q=b^\top\}$, the mean squared deviation of $Q$ is $\mathrm{MSD}(Q)=(Qv)^\top G(Qv)$, and $Q$ is **f-efficient** if $Q\in\mathscr D(q,b)$ and $\mathrm{MSD}(Q)\le\mathrm{MSD}(Q')$ for every $Q'\in\mathscr D(q,b)$ (Definition 1). Let $Q^{\mathrm{diversified}}=\frac1T q b^\top$ be full diversification (Example 1) and $z=G^{-1}\mathbf 1_K$. Then
--   $$
--   Q^{\mathrm{diversified}}\ \text{is f-efficient}\iff q \text{ and } z \text{ are linearly dependent.}
--   $$
--
--   The theorem says exactly when the diversification benchmark minimizes the deviation of market capitalization from its fundamental value: only when the vector of total holdings points in the direction $G^{-1}\mathbf 1_K$ determined by the shock moments. Corollary 4.1 of the paper derives from it that full diversification is f-efficient in a completely homogeneous system and stops being so under small heterogeneity.
--
--   **Formalization Note** "Linearly dependent" is `¬ LinearIndependent ℝ ![q, zVec μ σ]`, the negation of linear independence of the family $(q,z)$. $G$, $\mathscr D$, MSD, f-efficiency, $z$ and Assumption 3 are the published definitions of `SystemicHoldings.FEfficient.Model`; f-efficiency is the argmin of Definition 1, not the characterization $Qv=y^*$. The vector $v$ is a free parameter: the paper derives it from the primitives by (3.1), and the theorem holds for every $v$ satisfying Assumption 3. The dimension conditions $N\ge2$ and $K\ge1$ of §4.1 are implied by Assumption 3 and $T\neq0$ and are not stated separately.
--
--   Differences from the source:
--   - encoding: $\sum_k q_k=\sum_i b_i=:T$, derived in the text from $\mathscr D\neq\emptyset$ (p. 11) → hypothesis `hT : ∑ k, q k = ∑ i, b i`; reason: the paper's standing relation for §4, which it obtains from the nonemptiness of $\mathscr D$; it holds in every instance the paper considers.
--   - encoding: $Q^{\mathrm{diversified}}=\frac1T q b^\top$ presupposes $T\neq0$ → hypothesis `hT0 : ∑ k, q k ≠ 0`; reason: the object of the theorem is undefined at $T=0$ (Lean's $1/0=0$ would give the zero matrix, which is not even feasible), so the hypothesis only excludes instances where the source's statement has no meaning; the paper never assumes $q\ge0$ or $T>0$ and neither is added.
--   - generalization: $v$ derived from the primitives by (3.1) → $v\in\mathbb R^N$ an arbitrary parameter subject to Assumption 3; reason: the theorem and its proof use only Assumption 3 about $v$, and $v$ does not depend on $Q$; the paper's $v$ is one instance.
-- source:
--   Awiszus, Capponi & Weber, Market Efficient Portfolios in a Systemic Economy, arXiv:2003.10121v3, p. 14, Theorem 4.2; proof: E-Companion pp. 11-12 (PDF 41-42), EC.1.3.5; Q^diversified: p. 11, Example 1, (4.1)

import Mathlib
import Definitions.Def_SystemicHoldings_FEfficient_Model
import Definitions.Def_SystemicHoldings_FEfficient_Supplement_Diversification

namespace SystemicHoldings.FEfficient.Supplement
open Matrix

/-- Theorem 4.2, p. 14 (Awiszus–Capponi–Weber, arXiv:2003.10121v3; proof E-Companion pp. 11–12):
under Assumption 2 (`σ_k > 0`), Assumption 3, `∑ q = ∑ b =: T` and `T ≠ 0`, full diversification
`Q^diversified = (1/T) q bᵀ` is f-efficient (Definition 1: feasible and MSD-minimal over `𝒟(q, b)`)
if and only if `q` and `z = G⁻¹ 1_K` are linearly dependent. -/
theorem theorem_4_2 {K N : ℕ} (μ σ : Fin K → ℝ) (hσ : ∀ k, 0 < σ k)
    (q : Fin K → ℝ) (b v : Fin N → ℝ)
    (hT : ∑ k, q k = ∑ i, b i) (hT0 : ∑ k, q k ≠ 0)
    (hA3 : Assumption3 b v) :
    IsFEfficient μ σ q b v (qDiversified q b) ↔
      ¬ LinearIndependent ℝ ![q, zVec μ σ] := by sorry

end SystemicHoldings.FEfficient.Supplement
