-- Prove2me | Theorems.Thm_PorteusSS_conv_exp_mem_CK
-- name    : PorteusSS.conv_exp_mem_CK
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T17:56:05.563455+00:00
-- url     : https://prove2.me/theorems/5679a03c-82f4-4ba4-b5ab-ddc94fae02f6
-- title:
--   Lemma 10 — convolving a $C_a(K)$ function with an exponential density gives a $C(K)$ function
-- statement:
--   Let $K \ge 0$, $a \in \mathbb R$ and $f \in C_a(K)$, and let $\varphi$ be the (negative) exponential density with parameter $\lambda > 0$, $\varphi(t) = \lambda e^{-\lambda t}$ for $t \ge 0$ and $\varphi(t) = 0$ for $t < 0$. Then
--   $$ f * \varphi \in C(K). $$
--
--   This is the exponential special case of Theorem 1; the general case is obtained by approximating a one-sided Pólya density by finite convolutions of exponential densities.
-- source:
--   Porteus, On the Optimality of Generalized (s, S) Policies, Management Science 17(7):411–426 (1971), p. 424, Lemma 10

import Mathlib
import Definitions.Def_PorteusSS_Functions

open MeasureTheory Filter Topology Set

namespace PorteusSS

/-- Lemma 10 (p. 424). If `f ∈ C_a(K)` for `a ∈ ℝ` and `φ` is the exponential density with
parameter `lam > 0`, then `f * φ ∈ C(K)`. -/
theorem conv_exp_mem_CK (a K lam : ℝ) (f : ℝ → ℝ) (hf : CaK a K f) (hlam : 0 < lam) :
    CK K (conv f (expDensity lam)) := by sorry

end PorteusSS
