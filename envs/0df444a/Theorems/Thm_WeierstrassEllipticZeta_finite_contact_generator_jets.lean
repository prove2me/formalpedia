-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_finite_contact_generator_jets
-- name    : WeierstrassEllipticZeta.finite_contact_generator_jets
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-09T16:31:09.124396+00:00
-- url     : https://prove2.me/theorems/c923c7f6-00ce-4d33-b93f-cd357c467bd5
-- title:
--   Exact contact orders and quotient lengths for derivatives of finite generators
-- statement:
--   Fix an elliptic-extension chart with derivation $D$, a finite set
--   $V\subset\mathbb C^4$ and contact orders $n_v\in\mathbb N$. Let
--
--   $$I=\bigcap_{v\in V}C_v(n_v),\qquad
--   C_v(a)=\{p:D^jp(v)=0\text{ for }0\leq j<a\}.$$
--
--   Suppose a finite family $f_1,\ldots,f_r$ generates $I$. For each
--   $k\in\mathbb N$, form the ideal
--
--   $$K_k=(D^j f_i:1\leq i\leq r,\ 0\leq j\leq k).$$
--
--   Then
--
--   $$K_k=I+(D^kq:q\in I)
--   =\bigcap_{v\in V}C_v(\max(n_v-k,0)).$$
--
--   Its quotient is finite dimensional and satisfies
--
--   $$\dim_{\mathbb C}(\mathbb C[t,x,y,z]/K_k)
--   =\sum_{v\in V}\max(n_v-k,0).$$
--
--   Furthermore, $p\in K_k$ exactly when there is $q\in I$ with
--   $p-D^kq\in I$, and $K_k$ is the whole ring exactly when $n_v\leq k$
--   for every $v\in V$.
--
--   The result applies to every finite generating family. It includes empty
--   support and zero orders, without requiring distinct time coordinates
--   or a degree bound for the generators or primitive.
-- source:
--   Derived finite-generation calculation for the differential polynomial-ring method associated with Senthil Kumar K (2026), Appendix A introductory paragraphs and Theorem A.2, https://doi.org/10.1017/S001309152610145X. This exact generator-jet statement is derived here, not quoted from the article. Reuses the Proved elliptic_extension_contact_ideal_structure and finite_contact_iterated_differentiation. If a finite family generates a contact ideal, its derivatives through order k generate exactly the contact ideal with orders lowered by k and truncated at zero. The Leibniz rule controls differentiation of ideal combinations; induction and the one-step contact-differentiation theorem give the reverse inclusion. The general iterated-differentiation result supplies the dimension and primitive formulas. No particular generating family, distinct time coordinates or degree bounds are assumed.

import Definitions.Def_WeierstrassEllipticZeta_ProjectiveContactIdeal
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.Ideal.Quotient.Basic

open WeierstrassEllipticZeta
open scoped Classical

theorem WeierstrassEllipticZeta.finite_contact_generator_jets (g₂ g₃ : ℂ) (c : Fin 2)
    (V : Finset (Fin 4 → ℂ)) (n : V → ℕ) (r : ℕ)
    (f : Fin r → MvPolynomial (Fin 4) ℂ)
    (hgen : Ideal.span (Set.range f) =
      ⨅ v : V, extensionChartContactIdeal g₂ g₃ c v.val (n v)) (k : ℕ) :
    let I : Ideal (MvPolynomial (Fin 4) ℂ) :=
      ⨅ v : V, extensionChartContactIdeal g₂ g₃ c v.val (n v)
    let K := Ideal.span (Set.range (fun i : Fin (k + 1) × Fin r =>
      (extensionChartDerivation g₂ g₃ c)^[i.1.val] (f i.2)))
    K = I ⊔ Ideal.span ((extensionChartDerivation g₂ g₃ c)^[k] ''
      (I : Set (MvPolynomial (Fin 4) ℂ))) ∧
      K = (⨅ v : V, extensionChartContactIdeal g₂ g₃ c v.val (n v - k)) ∧
      FiniteDimensional ℂ (MvPolynomial (Fin 4) ℂ ⧸ K) ∧
      Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ K) = ∑ v : V, (n v - k) ∧
      (∀ p : MvPolynomial (Fin 4) ℂ,
        p ∈ K ↔ ∃ q : MvPolynomial (Fin 4) ℂ, q ∈ I ∧
          p - (extensionChartDerivation g₂ g₃ c)^[k] q ∈ I) ∧
      (K = ⊤ ↔ ∀ v : V, n v ≤ k) := by sorry
