-- Prove2me | Theorems.Thm_QuasilinearAG_Encoding_lemma_5_2
-- name    : QuasilinearAG.Encoding.lemma_5_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T15:43:11.406203+00:00
-- url     : https://prove2.me/theorems/c1437033-cc74-42b7-ba6d-8377ceaba846
-- title:
--   Lemma 5.2 — the intermediate step: $P_V$ additive over $\mathbb F_q$, $M_W\circ P_V=L$, $[E:F_{h-1}]=e$, $z^q+z=P_V(\phi(x_{h-1}))$, good fibres split into $D$ rational places
-- statement:
--   Let $q=p^s>2$, $k=\mathbb F_{q^2}$, $F_h$ the height-$h$ tower ($h\ge1$), $e=p^r$ ($1\le r\le s$), $V$ an $\mathbb F_p$-subspace of $C=\ker(X^q+X)$ of size $q/e$, $P_V=\prod_{v\in V}(X-v)$, $z=P_V(x_h)$, $E=F_{h-1}(z)$, $D=eq^{h-1}$. The polynomial $P_V$ is separable, additive, and has coefficients in $\mathbb F_q$. If $W=P_V(C)$ and $M_W(Z)=\prod_{w\in W}(Z-w)$, then
--   $$M_W\circ P_V=L,\qquad \deg M_W=e,\qquad M_W'\ne0,\qquad M_W(z)=\phi(x_{h-1}).\qquad(5.2)$$
--   Moreover $[E:F_{h-1}]=e$, and
--   $$z^q+z=P_V(\phi(x_{h-1})).\qquad(5.3)$$
--   There is a unique rational infinity place of $E$. Every good base place splits into $D$ distinct rational places in $E$.
--
--   Differences from the source:
--   - encoding: the tower F_h of (3.1) over k = F_{q^2}, q = p^s > 2 → any field F over any finite field k with q^2 elements (IsPrimePow q, 2 < q), with x_0 transcendental, (x_i^q + x_i)(1 + x_{i-1}^{q-1}) = x_{i-1}^q for 1 ≤ i ≤ h, and F = k(x_0, …, x_h) (IsGSTower); reason: every such F is a model of F_h; the division in φ is cleared, which excludes no instance
--   - encoding: places P and ord_P normalized to value group Z → Place k F: additive valuations F → Z ∪ {∞}, onto Z, zero on k^×; reason: places of a function field correspond one to one to their normalized valuations
--   - encoding: an F_p-subspace V ⊂ C of size q/e, e ∈ {p, …, q} → an additive subgroup V of k contained in {v : v^q + v = 0} with Nat.card V = q/e, e = p^r, 1 ≤ r ≤ s; reason: in characteristic p additive subgroups are exactly the F_p-subspaces
--   - encoding: P_V additive with coefficients in F_q → every nonzero coefficient sits at a degree p^i, and every coefficient c satisfies c^q = c; reason: over a field of characteristic p a polynomial is additive iff it is a linear combination of the X^{p^i}; F_q is the fixed field of c ↦ c^q
--   - encoding: [E : F_{h−1}] = e; unique rational infinity place; good base place splits into D distinct rational places → finrank of F_{h−1}(z) over F_{h−1} is e; exactly one place of E with ord x_0 < 0, and it has degree 1; for good β the places of E above x_0 = β number D (ncard) and have degree 1; reason: Lean names for the same statements
-- source:
--   Chao, Liu, Li, Ma, Wang, Quasilinear Encoding at the Quadratic Alphabet Scale via Short Cartier Bases, STOC 2027 submission (manuscript sha256 355c15dc…), p. 18, Lemma 5.2, (5.2)–(5.3) (PDF p. 20)

import Mathlib
import Definitions.Def_QuasilinearAG_Encoding_Tower
import Definitions.Def_QuasilinearAG_Encoding_Intermediate

namespace QuasilinearAG.Encoding

/-- Lemma 5.2 (Equations, degree and good fibres), p. 18 (PDF 20). Let `q = p^s > 2`,
`k = F_{q²}`, `F` the height-`h` second Garcia–Stichtenoth tower over `k` (`h ≥ 1`), `e = p^r` with
`1 ≤ r ≤ s`, and `V` an `F_p`-subspace of `C = ker(X^q + X) ⊂ k` with `|V| = q/e`. Put
`P_V = Π_{v ∈ V}(X - v)`, `z = P_V(x_h)`, `E = F_{h-1}(z)`, `D = e q^{h-1}`, `W = P_V(C)`,
`M_W = Π_{w ∈ W}(Z - w)`. Then `P_V` is separable, additive (only `p`-power exponents) with
coefficients in `F_q`; `M_W ∘ P_V = L = X^q + X`, `deg M_W = e`, `M_W' ≠ 0`,
`M_W(z) = ϕ(x_{h-1})` (5.2); `[E : F_{h-1}] = e`; `z^q + z = P_V(ϕ(x_{h-1}))` (5.3); `E` has a
unique place over `x₀ = ∞`, and it is rational; every good base place splits into `D` distinct
rational places of `E`. -/
theorem lemma_5_2 {k F : Type*} [Field k] [Fintype k] [Field F] [Algebra k F]
    (p s q h : ℕ) [Fact p.Prime] (hqs : q = p ^ s) (hq2 : 2 < q) (hk : Fintype.card k = q ^ 2)
    (hh : 1 ≤ h) (x : ℕ → F) (hx : IsGSTower k q h x)
    (r e : ℕ) (hr1 : 1 ≤ r) (hrs : r ≤ s) (he : e = p ^ r)
    (V : AddSubgroup k) (hVC : ∀ v ∈ V, v ^ q + v = 0) (hVcard : Nat.card V = q / e) :
    (subspacePoly V).Separable ∧
      (∀ n, (subspacePoly V).coeff n ≠ 0 → ∃ i : ℕ, n = p ^ i) ∧
      (∀ n, (subspacePoly V).coeff n ^ q = (subspacePoly V).coeff n) ∧
      (imagePoly q V).comp (subspacePoly V) = Polynomial.X ^ q + Polynomial.X ∧
      (imagePoly q V).natDegree = e ∧
      Polynomial.derivative (imagePoly q V) ≠ 0 ∧
      Polynomial.aeval (zElt h x V) (imagePoly q V) = phiField q (x (h - 1)) ∧
      Module.finrank (lowerField (k := k) x (h - 1))
          (IntermediateField.adjoin (lowerField (k := k) x (h - 1)) {zElt h x V}) = e ∧
      zElt h x V ^ q + zElt h x V = Polynomial.aeval (phiField q (x (h - 1))) (subspacePoly V) ∧
      (∃! P : Place k (interField h x V), P.v (x0InE h x V) < 0) ∧
      (∀ P : Place k (interField h x V), P.v (x0InE h x V) < 0 → P.deg = 1) ∧
      ∀ β : k, IsGood q β →
        {P : Place k (interField h x V) | P.Above (x0InE h x V) β}.ncard = e * q ^ (h - 1) ∧
        ∀ P : Place k (interField h x V), P.Above (x0InE h x V) β → P.deg = 1 := by sorry

end QuasilinearAG.Encoding
