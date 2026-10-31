-- Prove2me | Theorems.Thm_TRSHolderKL_lemma_3_5
-- name    : TRSHolderKL.lemma_3_5
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:56:41.303834+00:00
-- url     : https://prove2.me/theorems/6f51cd9a-c58e-4524-b2ff-13266594189d
-- title:
--   Lemma 3.5 — Wang–Pang error bound for convex quadratic systems
-- statement:
--   Let $q_i(x)\le0$, $i\in[m]$, be a system of convex quadratic inequalities on $\mathbb R^n$ with nonempty solution set $S$, and let $[m]=K\oplus J$, where $K$ indexes the nonsingular and $J$ the singular inequalities. Let $d$ be the degree of singularity of the system (Definition 3.4). Then there is $\tau>0$ such that
--   $$
--   \operatorname{dist}(x,S)\le\tau\Big(\sum_{i=1}^m[q_i(x)]_+ +\sum_{j\in J}[q_j(x)]_+^{1/2^d}\Big)\qquad\text{for all }x\in\mathbb R^n,
--   $$
--   where $[t]_+=\max\{t,0\}$.
--
--   This is Theorem 3.1 of Wang and Pang (1994), rescaled as in footnote 2 of the paper. It is the engine of all the error bounds for the TRS: the modulus depends only on the computable degree of singularity.
--
--   **Formalization Note** A convex quadratic is $x^TQx+c^Tx+d$ with $Q\succeq0$; nonlinear means not affine. The power is the real power of a nonnegative number.
--
--   Differences from the source:
--   - encoding: a convex quadratic system; a nonlinear inequality → each q_i is x ↦ ⟪x, Qx⟫ + ⟪c, x⟫ + d with Q positive semidefinite (IsConvexQuadratic); nonlinear means q_i is not affine; reason: the same functions; for such q_i not affine is Q ≠ 0
--   - reading: Definitions 3.2–3.3: "critical" subsystem, "become nonsingular", "contained in no critical subsystem" → a subsystem is any set of indices, judged against its own solution set; reason: the paper's computations on p.6 (d = 1 for (3) when min f < f*) and p.7 ("the only critical subsystem of (3) is the first inequality", d = 2) hold under this reading and fail under the reading that judges subsystems against the whole system's solution set (that reading gives d = 1 on p.7)
--   - generalization: ℝⁿ under the paper's blanket assumption n ≥ 2 (p.1) → any n and any m; reason: the blanket assumption avoids the trivial TRS and Lemma 3.5 does not need it; at n ≥ 2 the Lean statement is the source's
--   - encoding: [m] = K ⊕ J with K the nonsingular and J the singular indices → J is the filter of the singular indices and K is not named; reason: K occurs in no formula of (2), where the first sum runs over all of [m]
-- source:
--   Jiang and Li, Hölderian error bounds and Kurdyka-Łojasiewicz inequality for the trust region subproblem, arXiv:1911.11955v2, Lemma 3.5 and display (2), p.5 (Theorem 3.1 of Wang and Pang, Optimization 31(1):1–12, 1994)

import Mathlib
import Definitions.Def_RBMSensitivity_E
import Definitions.Def_TRSHolderKL_IsConvexQuadratic
import Definitions.Def_TRSHolderKL_solSet
import Definitions.Def_TRSHolderKL_IsSingularIn
import Definitions.Def_TRSHolderKL_degree

open scoped InnerProductSpace
open RBMSensitivity (E)

namespace TRSHolderKL

open Classical in
/-- Lemma 3.5, Jiang and Li, arXiv:1911.11955v2, display (2), p.5 (Theorem 3.1 of Wang and
Pang). Let `qᵢ(x) ≤ 0, i ∈ [m]`, be a convex quadratic system on `ℝⁿ` with nonempty solution
set `S`, and let `J` be the index set of its singular constraints. Then there is `τ > 0` with
`dist(x, S) ≤ τ (∑ᵢ [qᵢ(x)]₊ + ∑_{j ∈ J} [q_j(x)]₊^{1/2^d})` for all `x ∈ ℝⁿ`, where `d` is the
degree of singularity of the system.

**Formalization Note.** `[t]₊ = max t 0`; the power is `Real.rpow` with exponent `1/2^d`.
`dist(x, S)` is `Metric.infDist`. `[m]` is `Fin m`. `n` and `m` are arbitrary (the paper's
`n ≥ 2` is a blanket assumption for the TRS), and `K` is not named: it occurs in no formula of (2). -/
theorem lemma_3_5 {n m : ℕ} (q : Fin m → E n → ℝ) (hq : ∀ i, IsConvexQuadratic (q i))
    (hS : (solSet q Finset.univ).Nonempty) :
    ∃ τ : ℝ, 0 < τ ∧ ∀ x : E n,
      Metric.infDist x (solSet q Finset.univ) ≤
        τ * (∑ i, max (q i x) 0 +
          ∑ j ∈ Finset.univ.filter (fun j => IsSingularIn q Finset.univ j),
            (max (q j x) 0) ^ ((1 : ℝ) / (2 : ℝ) ^ degree q)) := by sorry

end TRSHolderKL
