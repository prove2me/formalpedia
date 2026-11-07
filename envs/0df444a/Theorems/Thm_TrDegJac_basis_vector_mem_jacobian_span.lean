-- Prove2me | Theorems.Thm_TrDegJac_basis_vector_mem_jacobian_span
-- name    : TrDegJac.basis_vector_mem_jacobian_span
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:37:15.920059+00:00
-- url     : https://prove2.me/theorems/fb6e6493-aaad-490d-85ec-b596531ce6c8
-- title:
--   Separability step (proof of Theorem 4.12) — $e_i\in\operatorname{col-span}_{\mathbb F(x)}\mathrm{Jac}_x(h)$ when $[\mathbb F(h,x_i):\mathbb F(h)]<p$
-- statement:
--   Let $\mathbb F$ be a field of prime characteristic $p$, let $h_1,\dots,h_N\in\mathbb F[x_1,\dots,x_n]$, and let $i\in\{1,\dots,n\}$. If
--   $$
--   [\mathbb F(h,x_i):\mathbb F(h)]<p,
--   $$
--   then the standard basis vector $e_i\in\mathbb F(x)^n$ lies in the column span of $\mathrm{Jac}_x(h)$ over $\mathbb F(x)$.
--
--   In the proof of Theorem 4.12 this is applied to $h=g\cup B\cup\{x_1,\dots,x_{k-1}\}$ for every $i$, so that $\mathrm{Jac}_x(h)$ has full rank $n$.
--
--   **Formalization Note** The degree is `Module.rank` of `IntermediateField.adjoin F(h) {x_i}` over $\mathbb F(h)$, so the hypothesis includes finiteness. The column span is the range of $v\mapsto\mathrm{Jac}_x(h)\,v$ and $e_i$ is `Pi.single i 1`.
--
--   Differences from the source:
--   - generalization: h = g ∪ B ∪ {x₁, …, x_{k−1}} as constructed in the proof → any finite family h : Fin N → F[x]; reason: the step (Proposition 4.4, clearing denominators, Lemma 4.6) uses only [F(h, x_i) : F(h)] < p; the proof's h is an instance
--   - encoding: char F = p, [F(h, x_i) : F(h)] < p, e_i ∈ col-span_{F(x)} Jac_x(h) → [CharP F p] with p prime, Module.rank < (p : Cardinal), Pi.single i 1 ∈ range of the map v ↦ Jac(h) v; reason: the same conditions; the rank bound also asserts finiteness
-- source:
--   Forbes and Staicu, Approximating Transcendence Degree in Medium Characteristic, STOC 2027 submission (manuscript sha256 3ab72a42…), Proof of Theorem 4.12, pp.29–30

import Mathlib
import Definitions.Def_TrDegJac_RatFn
import Definitions.Def_TrDegJac_jacobian
import Definitions.Def_TrDegJac_adjoinFamily

set_option autoImplicit false

namespace TrDegJac

/-- **Separability step in the proof of Theorem 4.12** — Forbes and Staicu, *Approximating Transcendence Degree in Medium Characteristic*, STOC 2027
submission (manuscript sha256 3ab72a42…), Proof of Theorem 4.12, pp.29–30:
"[F(h, x_i) : F(h)] ≤ … < p" (p.29), then "By Proposition 4.4, there exists a minimum degree
non-zero polynomial P_i ∈ F(h)[z] with deg_z P_i < p, … This implies e_i ∈ col-span_{F(x)} Jac_x(h)"
(p.30).

If `char F = p` is prime and the degree of `F(h, x_i)` over `F(h)` is less than `p`, then the
standard basis vector `e_i` lies in the column span over `F(x)` of the Jacobian of `h`.

**Formalization Note.** `h` is any finite family of polynomials (`Fin N → F[x]`); the paper's `h` is
`g ∪ B ∪ {x₁, …, x_{k−1}}`, but the step uses nothing about it. `[F(h, x_i) : F(h)]` is the
`Module.rank` of `IntermediateField.adjoin F(h) {x_i}` over `F(h)`, a cardinal, so the hypothesis
includes finiteness. The column span is the range of `v ↦ Jac(h) · v` over `F(x)`, and `e_i` is
`Pi.single i 1`. -/
theorem basis_vector_mem_jacobian_span {F : Type*} [Field F] (p : ℕ) [CharP F p] (hp : p.Prime)
    {n N : ℕ} (h : Fin N → MvPolynomial (Fin n) F) (i : Fin n)
    (hdeg : Module.rank (adjoinFamily h)
        (IntermediateField.adjoin (adjoinFamily h) {toRatFn (MvPolynomial.X i : MvPolynomial (Fin n) F)}) < (p : Cardinal)) :
    (Pi.single i 1 : Fin n → RatFn F n) ∈ LinearMap.range (jacobian h).mulVecLin := by sorry

end TrDegJac
