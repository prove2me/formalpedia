-- Prove2me | Theorems.Thm_PWDB_proposition_C_7
-- name    : PWDB.proposition_C_7
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:36:59.992572+00:00
-- url     : https://prove2.me/theorems/6eb6868e-c6aa-4acd-95a1-e4da6bc876e2
-- title:
--   Proposition C.7 — conjugates of partial conjugates
-- statement:
--   Let $E, F$ be finite-dimensional real inner product spaces and $f : E \times F \to \overline{\mathbb R}$ such that $f(\cdot, z)$ is closed and convex for every $z$ and $-f(x, \cdot)$ is closed and convex for every $x$. Then, with conjugates taken jointly on $E \times F$,
--   $$
--   (f^{*1})^* = (-f)^{*2} \qquad\text{and}\qquad ((-f)^{*2})^* = f^{*1}.
--   $$
--
--   This identity computes the conjugates in the dual of (P-W′) and so connects (P-W′) and (D-B′).
--
--   Differences from the source:
--   - generalization: ℝ^{dx}, ℝ^{dz} → finite-dimensional real inner product spaces E, F; reason: every ℝ^d with the dot product is such a space, so the Lean statement specializes to the printed one
--   - encoding: closed and convex extended-real functions; conjugates of functions on ℝ^{dx} × ℝ^{dz} → IsClosedFn ∧ IsConvexFn; conj on WithLp 2 (E × F) with ⟨(w, z), (x, y)⟩ = ⟨w, x⟩ + ⟨z, y⟩; reason: p.39's notions; the L² product inner product is that of ℝ^{dx} × ℝ^{dz}
-- source:
--   Zhen, Kuhn & Wiesemann, A Unified Theory of Robust and Distributionally Robust Optimization via the Primal-Worst-Equals-Dual-Best Principle, arXiv:2105.00760v2 (19 Jul 2023), Proposition C.7, p.69

import Mathlib
import Definitions.Def_PWDB_IsClosedFn
import Definitions.Def_PWDB_IsConvexFn
import Definitions.Def_PWDB_conj
import Definitions.Def_PWDB_PartialConj

namespace PWDB

/-- **Proposition C.7 (Conjugates of Partial Conjugates)** (Zhen, Kuhn & Wiesemann,
arXiv:2105.00760v2, Proposition C.7, p.69): "If `f : ℝ^{dx} × ℝ^{dz} → R̄` is closed and convex in
its first argument, and `−f` is closed and convex in its second argument, then `(f∗1)∗ = (−f)∗2`
and `((−f)∗2)∗ = f∗1`."

**Formalization Note** `f` is extended-valued and need not be proper; "closed" is the paper's
notion (p.39, `IsClosedFn`), "convex" is convexity of the epigraph (`IsConvexFn`). The conjugates
`(f∗1)∗` and `((−f)∗2)∗` are taken jointly in both arguments, on the Euclidean product
`WithLp 2 (E × F)`, whose inner product `⟨(w, z), (x, y)⟩ = ⟨w, x⟩ + ⟨z, y⟩` is that of
`ℝ^{dx} × ℝ^{dz}`. `(−f)∗2` is `pconj2 (fun x z => -f x z)`. -/
theorem proposition_C_7 {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] (f : E → F → EReal)
    (h₁ : ∀ z, IsClosedFn (fun x => f x z) ∧ IsConvexFn (fun x => f x z))
    (h₂ : ∀ x, IsClosedFn (fun z => -f x z) ∧ IsConvexFn (fun z => -f x z)) :
    conj (fun q : WithLp 2 (E × F) => pconj1 f (WithLp.ofLp q).1 (WithLp.ofLp q).2) =
      (fun q : WithLp 2 (E × F) =>
        pconj2 (fun x z => -f x z) (WithLp.ofLp q).1 (WithLp.ofLp q).2) ∧
    conj (fun q : WithLp 2 (E × F) =>
        pconj2 (fun x z => -f x z) (WithLp.ofLp q).1 (WithLp.ofLp q).2) =
      (fun q : WithLp 2 (E × F) => pconj1 f (WithLp.ofLp q).1 (WithLp.ofLp q).2) := by sorry

end PWDB
