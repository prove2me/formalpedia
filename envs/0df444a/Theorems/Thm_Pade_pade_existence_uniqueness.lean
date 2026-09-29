-- Prove2me | Theorems.Thm_Pade_pade_existence_uniqueness
-- name    : Pade.pade_existence_uniqueness
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-21T10:27:38.002217+00:00
-- url     : https://prove2.me/theorems/cc26c107-4a88-46f3-ad08-12008343953d
-- title:
--   Existence and uniqueness of the $[m/n]$ Padé approximant
-- statement:
--   **Fundamental theorem of Padé approximation (Frobenius).** Let $F$ be a field, let $f \in F[[x]]$ be a formal power series and let $m, n \ge 0$ be integers. Call $(P,Q)$ a *Padé pair of type $[m/n]$ for $f$* when $Q \ne 0$, $\deg P \le m$, $\deg Q \le n$ and $Qf - P \equiv 0 \pmod{x^{m+n+1}}$. Then:
--
--   $$ \textbf{(E)}\quad \text{a Padé pair of type } [m/n] \text{ for } f \text{ exists;} $$
--
--   $$ \textbf{(U)}\quad \text{if } (P_1,Q_1) \text{ and } (P_2,Q_2) \text{ are Padé pairs of type } [m/n] \text{ for } f, \text{ then } P_1Q_2 = P_2Q_1 . $$
--
--   Part (E) holds for every $f$, $m$ and $n$, with no condition on $f$; part (U) is the precise sense in which "the Padé approximant is unique as a formal power series for the given $m$ and $n$": two solutions need not be equal as pairs — they may differ by a common polynomial factor or a scalar — but they cross-multiply, hence define the same element of the field of rational functions $F(x)$.
--
--   Together the two parts make the Padé table $\big([m/n]_f\big)_{m,n\ge0}$ a well-defined array, which is the foundation for every identity relating its entries and for every algorithm (extended Euclid, Wynn's $\varepsilon$-algorithm) that computes them.
-- source:
--   Padé approximant, Wikipedia, revision oldid=1374746248, https://en.wikipedia.org/w/index.php?title=Pad%C3%A9_approximant&oldid=1374746248, section 'Definition' ('When it exists, the Padé approximant is unique as a formal power series for the given m and n.')

import Mathlib
import Definitions.Def_pade_approximant_def
open Polynomial

namespace Pade

theorem pade_existence_uniqueness {F : Type*} [Field F] (f : PowerSeries F) (m n : ℕ) :
    (∃ P Q : Polynomial F, IsPadeApproximant f m n P Q) ∧
      (∀ P₁ Q₁ P₂ Q₂ : Polynomial F, IsPadeApproximant f m n P₁ Q₁ →
        IsPadeApproximant f m n P₂ Q₂ → P₁ * Q₂ = P₂ * Q₁) := by sorry

end Pade
