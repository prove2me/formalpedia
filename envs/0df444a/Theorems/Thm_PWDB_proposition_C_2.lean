-- Prove2me | Theorems.Thm_PWDB_proposition_C_2
-- name    : PWDB.proposition_C_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:37:51.05003+00:00
-- url     : https://prove2.me/theorems/55095dd3-0bdf-4960-89f4-ccf1a0273fb4
-- title:
--   Proposition C.2 — the convex perspective is proper, closed and convex
-- statement:
--   Let $E$ be a finite-dimensional real inner product space and $f : E \to \overline{\mathbb R}$ proper, closed and convex. Then its convex perspective $(x, t) \mapsto t f(x/t)$ (Definition A.2, with $0 f(x/0) = \delta^*_{\operatorname{dom} f^*}(x)$) is proper, closed and convex on $E \times \mathbb R_+$.
--
--   This is what makes (D), (P-W′) and (D-B′) convex problems.
--
--   Differences from the source:
--   - generalization: ℝ^{dx}, ℝ^{dz} → finite-dimensional real inner product spaces E, F; reason: every ℝ^d with the dot product is such a space, so the Lean statement specializes to the printed one
--   - encoding: (F): fi proper, closed and convex, values in R̄ → TensorAHPE.IsProperClosedConvex (never −∞, somewhere finite, lower semicontinuous, convex epigraph), values in EReal; reason: for a proper function the paper's 'closed' (p.39) is lower semicontinuity; same instances
--   - encoding: convex perspective on ℝ^{dx} × ℝ₊ (Definitions A.2, A.4) → persp/pPersp with value +∞ for t < 0; reason: every multiplier in the paper is ≥ 0; no value at t ≥ 0 changes
--   - encoding: the convex perspective as a function of the pair (x, t) → a function on WithLp 2 (E × ℝ); reason: WithLp 2 (E × ℝ) has the topology and linear structure of E × ℝ
-- source:
--   Zhen, Kuhn & Wiesemann, A Unified Theory of Robust and Distributionally Robust Optimization via the Primal-Worst-Equals-Dual-Best Principle, arXiv:2105.00760v2 (19 Jul 2023), Proposition C.2, p.65; Definition A.2, p.39

import Mathlib
import Definitions.Def_TensorAHPE_IsProperClosedConvex
import Definitions.Def_PWDB_persp

namespace PWDB

/-- **Proposition C.2 (Properties of Convex Perspective Functions)** (Zhen, Kuhn & Wiesemann,
arXiv:2105.00760v2, Proposition C.2, p.65): "If `f : ℝ^{dx} → R̄` is proper, closed and convex, then
its convex perspective is also proper, closed and convex."

**Formalization Note** "Proper, closed and convex" is `TensorAHPE.IsProperClosedConvex`. The
convex perspective (Definition A.2, p.39) is `persp g`, viewed as a function of `(x, t)` on the
Euclidean product `WithLp 2 (E × ℝ)`; the paper's perspective lives on `ℝ^{dx} × ℝ₊`, and `persp`
extends it by `+∞` to `t < 0`, so that its properness, closedness and convexity on the whole space
is the paper's on `ℝ^{dx} × ℝ₊` (the extended-value convention for functions on a subset). -/
theorem proposition_C_2 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (g : E → EReal) (hg : TensorAHPE.IsProperClosedConvex g) :
    TensorAHPE.IsProperClosedConvex
      (fun q : WithLp 2 (E × ℝ) => persp g (WithLp.ofLp q).1 (WithLp.ofLp q).2) := by sorry

end PWDB
