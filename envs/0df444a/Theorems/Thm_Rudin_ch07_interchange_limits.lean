-- Prove2me | Theorems.Thm_Rudin_ch07_interchange_limits
-- name    : Rudin.ch07_interchange_limits
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-12T23:18:04.331987+00:00
-- url     : https://prove2.me/theorems/66f55fe8-cae1-456d-b8bd-806d99b4ae7d
-- title:
--   Theorem 7.11 — interchanging two limits
-- statement:
--   Suppose $f_n \to g$ uniformly on $E$, $x$ is a limit point of $E$, and $\lim_{t \to x} f_n(t) = A_n$ for each $n$. Then $\{A_n\}$ converges and $\lim_{t \to x} g(t) = \lim_n A_n$; in other words the two limit operations commute.
-- source:
--   Walter Rudin, Principles of Mathematical Analysis, 3rd edition, McGraw-Hill, 1976, Chapter 7, p. 149, Theorem 7.11

import Mathlib
import Definitions.Def_Rudin_ch07_families

open Filter Topology

namespace Rudin

/-- Rudin, Theorem 7.11: if `f n → g` uniformly on `E`, `x` is a limit point of `E`, and
`f n t → A n` as `t → x` within `E`, then `A n` converges and `g t → lim A n` as `t → x`;
that is, the two limit operations may be interchanged. -/
theorem ch07_interchange_limits {X : Type*} [MetricSpace X] (E : Set X) (f : ℕ → X → ℂ)
    (g : X → ℂ) (A : ℕ → ℂ) (x : X) (hx : x ∈ closure (E \ {x}))
    (huc : TendstoUniformlyOn f g atTop E)
    (hA : ∀ n, Tendsto (f n) (𝓝[E \ {x}] x) (𝓝 (A n))) :
    ∃ L : ℂ, Tendsto A atTop (𝓝 L) ∧ Tendsto g (𝓝[E \ {x}] x) (𝓝 L) := by sorry

end Rudin
