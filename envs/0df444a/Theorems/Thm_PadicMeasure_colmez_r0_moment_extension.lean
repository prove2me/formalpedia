-- Prove2me | Theorems.Thm_PadicMeasure_colmez_r0_moment_extension
-- name    : PadicMeasure.colmez_r0_moment_extension
-- status  : Proved
-- author  : @davidloeffler
-- created : 2026-09-06T01:44:01.174068+00:00
-- url     : https://prove2.me/theorems/3e5c9415-b672-4f83-9402-7226012e7f04
-- title:
--   Colmez order-zero extension of compatible polynomial disk moments
-- statement:
--   Let $p$ be a prime, $d\ge0$ an integer, and let $M_j(n,a)\in\mathbf C_p$ be prescribed moments for $0\le j\le d$, positive depths $n$, and integer centres $a$ prime to $p$.
--
--   Assume the degree-zero masses depend only on the residue class of $a$ modulo $p^n$. Assume each degree is compatible with subdivision:
--   $$M_j(n,a)=\sum_{b=0}^{p-1}M_j(n+1,a+bp^n).$$
--   Finally, assume that one constant $C\ge0$ satisfies
--   $$\left|\sum_{t=0}^{j}\binom jt(-a)^{j-t}M_t(n,a)\right|_p\le C p^{-nj}$$
--   for all such centres, depths, and degrees.
--
--   Then there exists exactly one bounded $\mathbf C_p$-valued measure $\mu$ on $\mathbf Z_p^\times$ such that
--   $$\int_{a+p^n\mathbf Z_p}x^j\,d\mu(x)=M_j(n,a)\qquad(0\le j\le d).$$
--
--   This is the order-zero polynomial-moment extension criterion associated with Colmez's extension theorem, restricted to the compact open unit group. It gives the higher moments as well as the masses.
--
--   **Formalization Note** Measures are continuous $\mathbf C_p$-linear functionals on continuous functions. The conclusion explicitly supplies continuous disk test functions with the specified pointwise values. Only degree-zero representative independence is assumed: after extending the masses, refinement and centred decay force agreement with every higher prescribed moment, by the Riemann-sum argument in Colmez's proof. The parameters of $M$ are degree, depth, and integer centre, in that order.
-- source:
--   Pierre Colmez, Fonctions d'une variable p-adique, Astérisque 330 (2010), pp. 13–59; author PDF https://webusers.imj-prg.fr/~pierre.colmez/fonctionsdunevariable.pdf, §II.3.2–3, Théorème II.3.2(ii), printed PDF pp. 32–33 and its proof, specialized to r=0 and L=Cp and restricted to Zp*. The degree-zero extension is described on PDF p. 31. Integer-centre moment presentation; higher representative independence follows from the vanishing argument on PDF p. 33.

import Mathlib.NumberTheory.Padics.Complex
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.NumberTheory.Padics.Measure.Basic

set_option autoImplicit false
noncomputable section
open scoped BigOperators

theorem PadicMeasure.colmez_r0_moment_extension
    {p : ℕ} [Fact p.Prime] (d : ℕ)
    (M : ℕ → ℕ → ℤ → ℂ_[p])
    (hres : ∀ (n : ℕ), 0 < n → ∀ (a b : ℤ),
      IsCoprime a (p : ℤ) → IsCoprime b (p : ℤ) →
      (a : ZMod (p^n)) = (b : ZMod (p^n)) → M 0 n a = M 0 n b)
    (hadd : ∀ (j : ℕ), j ≤ d → ∀ (n : ℕ), 0 < n →
      ∀ (a : ℤ), IsCoprime a (p : ℤ) →
        (∑ b ∈ Finset.range p, M j (n+1) (a+(b : ℤ)*(p : ℤ)^n)) = M j n a)
    (hbound : ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ), 0 < n →
      ∀ (a : ℤ), IsCoprime a (p : ℤ) → ∀ (j : ℕ), j ≤ d →
        ‖∑ t ∈ Finset.range (j+1),
          (j.choose t : ℂ_[p]) * (-(a : ℂ_[p]))^(j-t) * M t n a‖ ≤
          C * ‖(p : ℂ_[p])^(n*j)‖) :
    ∃! μ : AbstractMeasure (ℤ_[p])ˣ ℂ_[p] ℂ_[p],
      ∀ (n : ℕ), 0 < n → ∀ (a : ℤ), IsCoprime a (p : ℤ) →
        ∀ (j : ℕ), j ≤ d → ∃ g : C((ℤ_[p])ˣ, ℂ_[p]),
          (∀ x, g x = if PadicInt.toZModPow n x.val = (a : ZMod (p^n))
            then (algebraMap ℚ_[p] ℂ_[p] (x.val : ℚ_[p]))^j else 0) ∧
          μ g = M j n a := by sorry
