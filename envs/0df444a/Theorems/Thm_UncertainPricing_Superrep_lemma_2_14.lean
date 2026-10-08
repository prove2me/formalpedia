-- Prove2me | Theorems.Thm_UncertainPricing_Superrep_lemma_2_14
-- name    : UncertainPricing.Superrep.lemma_2_14
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T07:49:51.878709+00:00
-- url     : https://prove2.me/theorems/b9fb67df-45cd-4acd-85c6-18675446bbab
-- title:
--   Lemma 2.14, p. 9 — μ̄ Hölder ⇒ lim_n Λ((S^n_t − ⟨B⟩_t)²) = 0, S^n_t = Σ_{i<n}(B_{t_{i+1}} − B_{t_i})², t_i = it/n
-- statement:
--   Let $\mathbf P$ be a nonempty set of martingale measures on $\Omega$ satisfying $H(\bar\mu)$, and suppose that the distribution function $\bar\mu$ is Hölder continuous. Fix $t\in[0,T]$, put $t_i=it/n$ and
--   $$S^n_t=\sum_{i=0}^{n-1}\big(B_{t_{i+1}}-B_{t_i}\big)^2 .$$
--   Let $\langle B\rangle_t\in\mathcal L$ be the universal quadratic variation of Lemma 2.10. Then
--   $$\lim_{n\to\infty}\Lambda\big((S^n_t-\langle B\rangle_t)^2\big)=0 .$$
--
--   The realized variance along a uniform grid therefore approximates the bracket in the superreplication sense, uniformly over the models in $\mathbf P$; this is the tool used to transfer the bracket bounds to the measures $Q\in\mathcal Q$.
--
--   **Formalization Note.** $\langle B\rangle_t$ is any $q\in\mathcal L$ with $q=A_t$ $P$-a.s. for every $P\in\mathbf P$ and every quadratic variation $A$ of $B$ under $P$ (Lemma 2.10; such $q$ are q.s. equal, and $\Lambda$ only sees q.s. classes). The limit is taken in `EReal`. $\mathbf P\ne\emptyset$ is added: for $\mathbf P=\emptyset$ every set is polar and $\Lambda\equiv-\infty$, so the limit is not $0$; the paper tacitly works with a nonempty family.
-- source:
--   Denis & Martini, arXiv:math/0607111v1, Lemma 2.14 and the definition of S^n_t before it, p. 9

import Mathlib
import Definitions.Def_UncertainPricing_Superrep_Setting

namespace UncertainPricing.Superrep

open MeasureTheory Filter Topology BoundedContinuousFunction

theorem lemma_2_14 (T : ℝ) (hT : 0 < T) (μU : StieltjesFunction ℝ) (hμU : IsDistFn T μU)
    (Ps : Set (Measure (Ω T))) (hPs : ∀ P ∈ Ps, IsMartingaleMeasure P ∧ HypU μU P)
    (hPne : Ps.Nonempty) (hHol : IsHolder T μU) (t : Set.Icc (0 : ℝ) T)
    (q : Ω T → ℝ) (hq : InL Ps q) (hqA : ∀ P ∈ Ps, ∀ A, IsQuadVar P A → q =ᵐ[P] A t) :
    Tendsto (fun n : ℕ => Lam Ps μU (fun ω =>
      ((∑ i ∈ Finset.range n,
        (evalR ω ((i + 1 : ℕ) * (t : ℝ) / n) - evalR ω ((i : ℕ) * (t : ℝ) / n)) ^ 2) - q ω) ^ 2))
      atTop (𝓝 0) := by sorry

end UncertainPricing.Superrep
