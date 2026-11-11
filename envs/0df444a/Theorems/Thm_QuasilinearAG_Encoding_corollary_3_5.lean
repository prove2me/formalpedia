-- Prove2me | Theorems.Thm_QuasilinearAG_Encoding_corollary_3_5
-- name    : QuasilinearAG.Encoding.corollary_3_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T15:41:51.351438+00:00
-- url     : https://prove2.me/theorems/6a8ae24e-fc7d-43bf-8f9d-d7d6e4ddb952
-- title:
--   Corollary 3.5 — the $u_a=C_0^\kappa(m_a)$ form an $R_0$-basis of $R_h$, every $U_\beta$ is invertible, and their poles lie in $A$ with $\deg A<(2q+1)D$
-- statement:
--   In the height-$h$ second Garcia–Stichtenoth tower over $k=\mathbb F_{q^2}$ ($q=p^s>2$, $h\ge1$), with $D=q^h$, $\kappa=\lceil\log_q h\rceil+1$, $Q_*=q^\kappa$: the $D$ functions $u_a=C_0^\kappa(m_a)$ form an $R_0$-basis of $R_h$, hence a $k(x_0)$-basis of $F_h$. Every matrix $U_\beta[P,a]=u_a(P)$ ($\beta$ good, $P$ above $x_0=\beta$) is invertible. Their poles are all contained in the effective divisor
--   $$A=\lfloor B_0/Q_*\rfloor+\sum_{P\text{ finite}}(e_P-1)P+(qD-2)P_\infty,\qquad \deg A<(2q+1)D,\qquad(3.15)$$
--   and its support is disjoint from every good evaluation point.
--
--   Differences from the source:
--   - encoding: the tower F_h of (3.1) over k = F_{q^2}, q = p^s > 2 → any field F over any finite field k with q^2 elements (IsPrimePow q, 2 < q), with x_0 transcendental, (x_i^q + x_i)(1 + x_{i-1}^{q-1}) = x_{i-1}^q for 1 ≤ i ≤ h, and F = k(x_0, …, x_h) (IsGSTower); reason: every such F is a model of F_h; the division in φ is cleared, which excludes no instance
--   - encoding: places P and ord_P normalized to value group Z → Place k F: additive valuations F → Z ∪ {∞}, onto Z, zero on k^×; reason: places of a function field correspond one to one to their normalized valuations
--   - encoding: R_0-basis of R_h; k(x_0)-basis of F_h → linear independence over R_0 with R_0-span equal to R_h; linear independence over k(x_0) with span ⊤; reason: definition of a basis
--   - encoding: U_β invertible → the map c ↦ (P ↦ Σ_a c_a u_a(P)) from k^D to functions on the places above β is bijective; reason: a matrix is invertible iff its map is bijective; this also says there are exactly D such places
--   - encoding: the divisor A, its degree, "poles contained in A", disjoint support → shortDivisor as a function on places: A ≥ 0, finite support, divDeg A < (2q+1)D, ord_P u_a ≥ −A(P), A(P) = 0 above good β; every place over x_0 = ∞ receives qD − 2; reason: the paper shows P_∞ is the only place over x_0 = ∞; finiteness of the support is part of A being a divisor
-- source:
--   Chao, Liu, Li, Ma, Wang, Quasilinear Encoding at the Quadratic Alphabet Scale via Short Cartier Bases, STOC 2027 submission (manuscript sha256 355c15dc…), p. 11, Corollary 3.5, (3.15) (PDF p. 13)

import Mathlib
import Definitions.Def_QuasilinearAG_Encoding_Tower

namespace QuasilinearAG.Encoding

/-- Corollary 3.5 (One extra extraction for coding), p. 11 (PDF 13). In the height-`h` second
Garcia–Stichtenoth tower `F` over `k = F_{q²}` (`q > 2` a prime power), with `D = q^h`,
`κ = ⌈log_q h⌉ + 1`, `Q* = q^κ` and `u_a = C₀^κ(m_a)`:
the `D` functions `u_a` form an `R₀`-basis of `R_h` (`R₀ = k[x₀, t⁻¹]`), hence a `k(x₀)`-basis of
`F`; for every good `β` (`β^q + β ≠ 0`) the evaluation matrix `U_β[P, a] = u_a(P)` on the places
`P` above `x₀ = β` is invertible; and the poles of all `u_a` lie in the effective divisor
`A = ⌊B₀/Q*⌋ + Σ_{P finite}(e_P - 1)P + (qD - 2)P_∞` (3.15), which has finite support,
`deg A < (2q + 1)D`, and support disjoint from every good evaluation point. -/
theorem corollary_3_5 {k F : Type*} [Field k] [Fintype k] [Field F] [Algebra k F]
    (q h : ℕ) (hq : IsPrimePow q) (hq2 : 2 < q) (hk : Fintype.card k = q ^ 2) (hh : 1 ≤ h)
    (x : ℕ → F) (hx : IsGSTower k q h x) :
    LinearIndependent (towerRing (k := k) q x 0) (extracted q h x) ∧
      ((Submodule.span (towerRing (k := k) q x 0) (Set.range (extracted q h x)) : Set F) =
        (towerRing (k := k) q x h : Set F)) ∧
      LinearIndependent (baseField (k := k) x) (extracted q h x) ∧
      Submodule.span (baseField (k := k) x) (Set.range (extracted q h x)) = ⊤ ∧
      (∀ β : k, IsGood q β → Function.Bijective (fibreEvalMap (x 0) β (extracted q h x))) ∧
      (∀ P : Place k F, 0 ≤ shortDivisor (k := k) q h x P) ∧
      (Function.support (shortDivisor (k := k) q h x)).Finite ∧
      divDeg (shortDivisor (k := k) q h x) < (2 * (q : ℤ) + 1) * (q : ℤ) ^ h ∧
      (∀ (a : Fin h → Fin q) (P : Place k F),
        ((-shortDivisor (k := k) q h x P : ℤ) : WithTop ℤ) ≤ P.v (extracted q h x a)) ∧
      (∀ β : k, IsGood q β → ∀ P : Place k F, P.Above (x 0) β →
        shortDivisor (k := k) q h x P = 0) := by sorry

end QuasilinearAG.Encoding
