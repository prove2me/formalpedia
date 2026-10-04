-- Prove2me | Theorems.Thm_PorteusSS_conv_polya_mem_CK
-- name    : PorteusSS.conv_polya_mem_CK
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T17:56:37.042602+00:00
-- url     : https://prove2.me/theorems/c5ad1bae-ba68-4076-8dc9-051297ae8696
-- title:
--   Theorem 1 — $C_a(K) * \varphi \subseteq C(K)$ for one-sided Pólya densities $\varphi$
-- statement:
--   Let $K \ge 0$ and $f \in C_a(K)$ for some $a \in \mathbb R$, and let $\varphi$ be a one-sided Pólya density. Then
--   $$ f * \varphi \in C(K), \qquad (f*\varphi)(y) = \int_{-\infty}^{\infty} f(y - x)\,\varphi(x)\,dx . $$
--
--   In particular the class $C(K)$ is closed under convolution with one-sided Pólya densities. This is the step that replaces Scarf's preservation of $K$-convexity under expectation: it shows that the expected future cost functions of the inventory model stay in the class that yields $(s,S)$-type decisions.
-- source:
--   Porteus, On the Optimality of Generalized (s, S) Policies, Management Science 17(7):411–426 (1971), p. 415, Theorem 1 (proof p. 425)

import Mathlib
import Definitions.Def_PorteusSS_Functions

open MeasureTheory Filter Topology Set

namespace PorteusSS

/-- Theorem 1 (p. 415). If `f ∈ C_a(K)` for some `a ∈ ℝ` and `φ` is a one-sided Pólya density,
then `f * φ ∈ C(K)`. -/
theorem conv_polya_mem_CK (a K : ℝ) (f φ : ℝ → ℝ) (hf : CaK a K f)
    (hφ : IsOneSidedPolyaDensity φ) :
    CK K (conv f φ) := by sorry

end PorteusSS
