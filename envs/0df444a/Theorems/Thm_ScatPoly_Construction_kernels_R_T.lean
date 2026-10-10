-- Prove2me | Theorems.Thm_ScatPoly_Construction_kernels_R_T
-- name    : ScatPoly.Construction.kernels_R_T
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T19:16:52.977174+00:00
-- url     : https://prove2.me/theorems/9adc6c1f-dd02-490e-adc1-18617099995d
-- title:
--   §3, p. 8, display (8) — R, T are 𝔽_{q^t}-linear, dim ker R = dim ker T = 1, ker T = h^{q^{t−1}−q} ker R
-- statement:
--   Let $q = p^r$ be an odd prime power, $t \ge 3$, $F = \mathbb F_{q^{2t}}$, $\mathbb F_{q^t} \subseteq F$ the subfield of order $q^t$, and $h \in F$ with $h^{q^t+1} = -1$. Consider
--   $$R(x) = x^{q^t} + h^{q^{t-1}-q} x, \qquad T(x) = x^{q^t} + h^{q-q^{t-1}} x. \tag{8}$$
--   Then:
--
--   1. $R$ and $T$ are $\mathbb F_{q^t}$-linear maps of $F$ (additive, and $R(\lambda x) = \lambda R(x)$, $T(\lambda x) = \lambda T(x)$ for $\lambda \in \mathbb F_{q^t}$);
--   2. $\ker R$ and $\ker T$ are 1-dimensional $\mathbb F_{q^t}$-subspaces of $F$ (containing $0$, closed under addition and $\mathbb F_{q^t}$-scalars, of cardinality $q^t$);
--   3. $$\ker T = h^{q^{t-1}-q}\,\ker R = \{h^{q^{t-1}-q}\rho : \rho \in \ker R\}.$$
--
--   The kernels of $R$ and $T$ describe exactly which multipliers carry $\ker M$ into $\ker L$ and $\ker L$ into $\ker M$ (Propositions 3.5, 3.6).
--
--   **Formalization Note.** $h^{q^{t-1}-q}$ is `h ^ q ^ (t-1) / h ^ q` and $h^{q-q^{t-1}}$ is `h ^ q / h ^ q ^ (t-1)`. "1-dimensional" is `IsFqSubspace` plus `HasRank … 1`.
-- source:
--   Longobardi, Marino, Trombetti & Zhou, A large family of maximum scattered linear sets of PG(1, q^n) and their associated MRD codes, arXiv:2102.08287v3, p. 8, §3, display (8) and the sentence after it

import Mathlib
import Definitions.Def_ScatCaps_LinearSets_Model
import Definitions.Def_ScatPoly_Construction_Model

namespace ScatPoly.Construction

open ScatCaps.LinearSets in
theorem kernels_R_T (F : Type*) [Field F] [Fintype F] (p r t q : ℕ) [Fact p.Prime] [CharP F p]
    (hp : Odd p) (hr : 0 < r) (hq : q = p ^ r) (ht : 3 ≤ t)
    (hcard : Fintype.card F = q ^ (2 * t))
    (h : F) (hh : h ^ (q ^ t + 1) = -1) :
    (∀ x y : F, Rmap q t h (x + y) = Rmap q t h x + Rmap q t h y) ∧
    (∀ x y : F, Tmap q t h (x + y) = Tmap q t h x + Tmap q t h y) ∧
    (∀ l ∈ subfieldOf F p r t, ∀ x : F, Rmap q t h (l * x) = l * Rmap q t h x) ∧
    (∀ l ∈ subfieldOf F p r t, ∀ x : F, Tmap q t h (l * x) = l * Tmap q t h x) ∧
    IsFqSubspace (subfieldOf F p r t) {x : F | Rmap q t h x = 0} ∧
    HasRank (subfieldOf F p r t) {x : F | Rmap q t h x = 0} 1 ∧
    IsFqSubspace (subfieldOf F p r t) {x : F | Tmap q t h x = 0} ∧
    HasRank (subfieldOf F p r t) {x : F | Tmap q t h x = 0} 1 ∧
    {x : F | Tmap q t h x = 0} =
      (fun x => h ^ q ^ (t - 1) / h ^ q * x) '' {x : F | Rmap q t h x = 0} := by sorry

end ScatPoly.Construction
