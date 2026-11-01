-- Prove2me | Theorems.Thm_PWDB_proposition_C_5
-- name    : PWDB.proposition_C_5
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:37:08.873407+00:00
-- url     : https://prove2.me/theorems/cdceb9a6-cc9f-4aec-8084-bc5c9b6aca3d
-- title:
--   Proposition C.5 — partial conjugates are jointly closed and convex
-- statement:
--   Let $E, F$ be finite-dimensional real inner product spaces and $f : E \times F \to \overline{\mathbb R}$.
--
--   1. If $-f(x, \cdot)$ is closed and convex for every $x$, then $f^{*1}(w,z) = \sup_x\{\langle w, x\rangle - f(x,z)\}$ is closed and convex jointly in $(w, z)$.
--   2. If $-f(\cdot, z)$ is closed and convex for every $z$, then $f^{*2}(x,y) = \sup_z\{\langle y, z\rangle - f(x,z)\}$ is closed and convex jointly in $(x, y)$.
--
--   "Closed" is Rockafellar's notion of p.39 (lower semicontinuous, and never $-\infty$ or identically $-\infty$); $f$ need not be proper. This is why (P-W′) is a convex problem.
--
--   Differences from the source:
--   - generalization: ℝ^{dx}, ℝ^{dz} → finite-dimensional real inner product spaces E, F; reason: every ℝ^d with the dot product is such a space, so the Lean statement specializes to the printed one
--   - encoding: closed and convex extended-real functions; joint closedness/convexity on ℝ^{dx} × ℝ^{dz} → IsClosedFn ∧ IsConvexFn, the joint ones on WithLp 2 (E × F); reason: IsClosedFn is p.39's definition, IsConvexFn is convexity of the epigraph; WithLp 2 (E × F) has the topology and linear structure of E × F
-- source:
--   Zhen, Kuhn & Wiesemann, A Unified Theory of Robust and Distributionally Robust Optimization via the Primal-Worst-Equals-Dual-Best Principle, arXiv:2105.00760v2 (19 Jul 2023), Proposition C.5, p.66

import Mathlib
import Definitions.Def_PWDB_IsClosedFn
import Definitions.Def_PWDB_IsConvexFn
import Definitions.Def_PWDB_PartialConj

namespace PWDB

/-- **Proposition C.5 (Properties of Partial Conjugates)** (Zhen, Kuhn & Wiesemann,
arXiv:2105.00760v2, Proposition C.5, p.66): "For any function `f : ℝ^{dx} × ℝ^{dz} → R̄`, the
partial conjugate `f∗1` is closed and convex (jointly in both arguments) if `−f` is closed and
convex in its second argument. Similarly, the partial conjugate `f∗2` is closed and convex if `−f`
is closed and convex in its first argument."

**Formalization Note** `f` is extended-valued and need not be proper. "Closed" is the paper's
notion (p.39, `IsClosedFn`: lower semicontinuous, and never `−∞` or identically `−∞`); "convex" is
convexity of the epigraph (`IsConvexFn`). Joint closedness and convexity are taken on the Euclidean
product `WithLp 2 (E × F)` (its topology and linear structure are those of `E × F`). -/
theorem proposition_C_5 {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] (f : E → F → EReal) :
    ((∀ x, IsClosedFn (fun z => -f x z) ∧ IsConvexFn (fun z => -f x z)) →
      IsClosedFn (fun q : WithLp 2 (E × F) => pconj1 f (WithLp.ofLp q).1 (WithLp.ofLp q).2) ∧
      IsConvexFn (fun q : WithLp 2 (E × F) => pconj1 f (WithLp.ofLp q).1 (WithLp.ofLp q).2)) ∧
    ((∀ z, IsClosedFn (fun x => -f x z) ∧ IsConvexFn (fun x => -f x z)) →
      IsClosedFn (fun q : WithLp 2 (E × F) => pconj2 f (WithLp.ofLp q).1 (WithLp.ofLp q).2) ∧
      IsConvexFn (fun q : WithLp 2 (E × F) => pconj2 f (WithLp.ofLp q).1 (WithLp.ofLp q).2)) := by sorry

end PWDB
