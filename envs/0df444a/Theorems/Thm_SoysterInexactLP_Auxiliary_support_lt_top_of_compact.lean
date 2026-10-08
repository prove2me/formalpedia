-- Prove2me | Theorems.Thm_SoysterInexactLP_Auxiliary_support_lt_top_of_compact
-- name    : SoysterInexactLP.Auxiliary.support_lt_top_of_compact
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:37:13.272666+00:00
-- url     : https://prove2.me/theorems/472128cd-c7aa-4ac5-a2a4-9c47ec3f75eb
-- title:
--   Compact activity sets have finite support functionals δ*(eᵢ|Kⱼ) < ∞
-- statement:
--   Let $K_1,\dots,K_n\subseteq\mathbb R^m$ be nonempty convex sets. If every $K_j$ is compact, then
--   $$\delta^*(e_i\mid K_j)<+\infty\qquad\text{for all } i=1,\dots,m,\ j=1,\dots,n.$$
--
--   So the finiteness assumption under which the auxiliary linear program LP$(\bar A)$ is defined holds automatically for compact activity sets, for instance for the hyperspheres of the inexact linear programming application.
--
--   **Formalization Note** Nonemptiness and convexity are the paper's standing assumptions and are kept although unused.
-- source:
--   Soyster, Convex Programming with Set-Inclusive Constraints and Applications to Inexact Linear Programming, Operations Research 21 (1973), p. 1156 (PDF p. 4), first paragraph

import Mathlib
import Definitions.Def_SoysterInexactLP_Auxiliary_Problems
open Pointwise Matrix

namespace SoysterInexactLP.Auxiliary

theorem support_lt_top_of_compact {m n : ℕ} (K : Fin n → Set (Fin m → ℝ))
    (hne : ∀ j, (K j).Nonempty) (hconv : ∀ j, Convex ℝ (K j))
    (hcpt : ∀ j, IsCompact (K j)) :
    ∀ i j, supportFun (K j) (Pi.single i 1) < ⊤ := by sorry

end SoysterInexactLP.Auxiliary
