-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_triangular_prefix_gcd_recurrence
-- name    : WeierstrassEllipticZeta.triangular_prefix_gcd_recurrence
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-09T19:53:59.122+00:00
-- url     : https://prove2.me/theorems/4ed70ef5-1627-4172-a933-2e3256e5251d
-- title:
--   Explicit gcd recurrence for triangular ideal prefixes
-- statement:
--   Let $A=\mathbb C[X_0,X_1,X_2,X_3]$ and let $\phi:A\to\mathbb C[T]$
--   be the substitution $X_0\mapsto T$, $X_{i+1}\mapsto r_i(T)$.
--   Suppose $M$ is monic and $I\subseteq A$ is an ideal with
--   $f\in I\iff M\mid\phi(f)$. For any sequence $(p_s)_{s\geq0}$ in $A$,
--   define
--
--   $$G_0=M,\qquad G_{s+1}=\gcd(G_s,\phi(p_s)),\qquad
--   J_s=I+(p_0,\ldots,p_{s-1}).$$
--
--   For every $s\geq0$, $G_s$ is monic and divides $M$, and
--   $f\in J_s\iff G_s\mid\phi(f)$. The quotient $A/J_s$ is finite dimensional
--   with $\dim_{\mathbb C}(A/J_s)=\deg G_s$.
--   Also $G_{s+1}\mid G_s$ and $\deg G_{s+1}\leq\deg G_s$, with
--
--   $$G_{s+1}=G_s\iff p_s\in J_s,$$
--   $$\deg G_{s+1}<\deg G_s\iff p_s\notin J_s,$$
--   $$\dim_{\mathbb C}(A/J_{s+1})<\dim_{\mathbb C}(A/J_s)
--   \iff p_s\notin J_s.$$
--
--   The assertion includes the empty prefix $s=0$ and the unit ideal.
-- source:
--   Derived commutative-algebra construction associated with Senthil Kumar K (2026), Appendix A and Theorem A.2, https://doi.org/10.1017/S001309152610145X. This recurrence is derived here, not quoted from the article. Starting from a monic triangular time relation M and a sequence p_s, define G_0=M and G_(s+1)=gcd(G_s,phi(p_s)). The theorem proves at every prefix that G_s is monic, divides M, gives the exact membership criterion and quotient dimension, and strictly drops in degree and quotient dimension exactly when the next equation is absent. Reuses the Proved canonical update and hypersurface intersection length theorems.

import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Ideal.Quotient.Operations

theorem WeierstrassEllipticZeta.triangular_prefix_gcd_recurrence
    (I : Ideal (MvPolynomial (Fin 4) ℂ)) (M : Polynomial ℂ)
    (r : Fin 3 → Polynomial ℂ) (hM : M.Monic)
    (hI : ∀ f : MvPolynomial (Fin 4) ℂ,
      f ∈ I ↔ M ∣ MvPolynomial.aeval (Fin.cons Polynomial.X r) f)
    (p : ℕ → MvPolynomial (Fin 4) ℂ) :
    let G : ℕ → Polynomial ℂ := Nat.rec M (fun s g =>
      gcd g (MvPolynomial.aeval (Fin.cons Polynomial.X r) (p s)))
    G 0 = M ∧
    (∀ s : ℕ, G (s + 1) = gcd (G s)
      (MvPolynomial.aeval (Fin.cons Polynomial.X r) (p s))) ∧
    ∀ s : ℕ,
      let J := I ⊔ Ideal.span (Set.range (fun i : Fin s => p i.val))
      (G s).Monic ∧ G s ∣ M ∧
      (∀ f : MvPolynomial (Fin 4) ℂ,
        f ∈ J ↔ G s ∣ MvPolynomial.aeval (Fin.cons Polynomial.X r) f) ∧
      FiniteDimensional ℂ (MvPolynomial (Fin 4) ℂ ⧸ J) ∧
      Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ J) = (G s).natDegree ∧
      G (s + 1) ∣ G s ∧ (G (s + 1)).natDegree ≤ (G s).natDegree ∧
      (G (s + 1) = G s ↔ p s ∈ J) ∧
      ((G (s + 1)).natDegree < (G s).natDegree ↔ p s ∉ J) ∧
      (Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸
          (I ⊔ Ideal.span (Set.range (fun i : Fin (s + 1) => p i.val)))) <
        Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ J) ↔ p s ∉ J) := by sorry
