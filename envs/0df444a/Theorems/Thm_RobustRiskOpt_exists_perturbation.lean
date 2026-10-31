-- Prove2me | Theorems.Thm_RobustRiskOpt_exists_perturbation
-- name    : RobustRiskOpt.exists_perturbation
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:43:02.49942+00:00
-- url     : https://prove2.me/theorems/7996553b-50e3-4646-92fb-95f900144eea
-- title:
--   p.30 — a small perturbation increases the mass of a set
-- statement:
--   Let $n\ge1$, $p\in(0,1)$, and let $\mu$ be a probability measure on $\mathbb R^n$ with a positive density on its support, which is a convex set. Let $A\subset\mathbb R^n$ be a Borel set with $\mu(A)=1-p$, and let $\varepsilon>0$. Then there is a Borel map $f:\mathbb R^n\to\mathbb R^n$ such that $|f(x)-x|\le\varepsilon$ for all $x$ and
--
--   $$
--   \mu(\{x:f(x)\in A\})>1-p.
--   $$
--
--   Taking $Z_\varepsilon=f(X)$ produces the perturbed model used in the proof of Theorem 1: it moves probability mass into $A$, although it stays within $\varepsilon$ of $X$.
--
--   Differences from the source:
--   - reading: f_ε is a Borel selection of nearest points of A on Ã_ε = {d(x, A) ⩽ ε}, and P(Z_ε ∈ A) = P(X ∈ Ã_ε) > 1 − p → there exists a Borel f with displacement at most ε and μ(f ∈ A) > 1 − p; reason: a Borel A need not have nearest points, so the printed map need not exist; the statement keeps what the proof uses from it
--   - generalization: A is a p-tail event of g_X → A is any Borel set of mass 1 − p; reason: a tail event is a special case
--   - encoding: μ_X has a positive density on its support, which is a convex subset of ℝⁿ → μ_X and Lebesgue measure restricted to a convex set S are mutually absolutely continuous; reason: the density is positive a.e. on S and zero a.e. off S; a convex set and its closure differ by a null set, so the instances are the same
--   - encoding: ℝⁿ with the Euclidean norm, n a positive integer → EuclideanSpace ℝ (Fin n) with 0 < n; reason: same space and norm
-- source:
--   Embrechts–Schied–Wang, Robustness in the Optimization of Risk Measures, arXiv:1809.09268v3, 11 Feb 2021, proof of Theorem 1, p.30 (the maps f_ε and the perturbation Z_ε)

import Mathlib
import Definitions.Def_ESAxioms_Characterization_Setting
import Definitions.Def_RobustRiskOpt_Admissible
import Definitions.Def_RobustRiskOpt_Assumptions

open MeasureTheory

namespace RobustRiskOpt

/-- p.30, in the proof of Theorem 1 (Embrechts–Schied–Wang, arXiv:1809.09268v3): for `μ` with a
positive density on a convex support and a Borel set `A` with `μ(A) = 1 − p`, every `ε > 0` admits a
Borel map `f` moving points by at most `ε` such that `μ(f ∈ A) > 1 − p`. Then `Z_ε := f(X)` is the
perturbation of the proof.

**Formalization Note** The printed `f_ε` is a Borel selection of nearest points of `A`, which need
not exist for a Borel `A`. The statement asks only for what the proof uses: a map into `A` on a
set of mass exceeding `1 − p`, with displacement at most `ε`. -/
theorem exists_perturbation {n : ℕ} (hn : 0 < n) (μ : Measure (E n)) [IsProbabilityMeasure μ]
    (hμ : HasConvexSupportDensity μ) (p : ℝ) (hp : p ∈ Set.Ioo (0 : ℝ) 1) (A : Set (E n))
    (hA : MeasurableSet A) (hμA : μ.real A = 1 - p) (ε : ℝ) (hε : 0 < ε) :
    ∃ f : E n → E n, Measurable f ∧ (∀ x, ‖f x - x‖ ≤ ε) ∧
      1 - p < μ.real {x | f x ∈ A} := by sorry

end RobustRiskOpt
