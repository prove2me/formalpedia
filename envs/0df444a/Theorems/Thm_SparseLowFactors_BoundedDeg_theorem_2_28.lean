-- Prove2me | Theorems.Thm_SparseLowFactors_BoundedDeg_theorem_2_28
-- name    : SparseLowFactors.BoundedDeg.theorem_2_28
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T06:23:49.5374+00:00
-- url     : https://prove2.me/theorems/6ea39b68-5533-4ef2-8929-0543ad2e0346
-- title:
--   Theorem 2.28 ([BKR+26]) — $R_e(Z)=A/B$ with small constant-depth circuits, $B(\beta)\neq0$, and $R_e(\beta)$ is the truncated root
-- statement:
--   Let $F$ be a field with $\mathrm{char}\,F=0$ or $>d$. Let $F(T,Y)\in F[X][T,Y]$ be monic in $Y$, with $\deg_YF=d$, $\deg_TF=D$, Hensel-ready at $T=0$ (over $F(X)$), with $F(0,Y)\in F[Y]$, and computed by a circuit of size $s'$ and depth $\Delta$. Let $\beta$ (in a field $L\supseteq F$) be a root of $F(0,Y)$ of multiplicity $e\ge1$, and let $R_e$ be the rational function of p. 24. There are universal constants $C,c_0$ such that:
--
--   1. $R_e(Z)=A(X,T,Z)/B(Z)$ with $A\in F[X,T,Z]$ and $0\neq B\in F[Z]$, both computed by circuits of size at most $C(n+s'+d+D)^C$ and depth at most $\Delta+c_0$;
--   2. $B(\beta)\neq0$;
--   3. $\Phi_\beta(T)\ \mathrm{Trunc}\ T^{D+1}=R_e(\beta)\ \mathrm{Trunc}\ T^{D+1}$.
--
--   This gives constant-depth circuits, with one division by a field constant, for truncations of the power-series roots.
--
--   **Formalization Note** $R_e(Z)$ lives in the field $F(X,T,Z)$; $R_e(\beta)$ is the same formula in $L[X][T]$ with $Z=\beta$. $\Phi_\beta(T)\in L[X][[T]]$ is the power-series root of $F$ with constant term $\beta$. Circuits are over $F$ in the variables $X_1,\dots,X_n,T,Y$ (for $F$) and $X_1,\dots,X_n,T,Z$ (for $A,B$).
--
--   Differences from the source:
--   - reading: F(T, Y) ∈ F[X][T, Y] with β a root of F(0, Y) and B(Z) ∈ F[Z] → hypothesis F(0, Y) ∈ F[Y] (the T-free part has X-free coefficients); reason: R_e is defined as a Laurent series in Z over F[X][T] (p. 24), which needs ∂^e_Y F(0, Z) to have constant leading data, and the roots β are field elements; in the paper F(T, Y) = f(TX, Y), for which F(0, Y) = f(0, Y) ∈ F[Y]
--   - reading: "Hensel-ready at T = 0" for F ∈ F[X][T, Y] → Hensel-ready at T = 0 as a polynomial in T, Y over the field F(X); reason: Definition 2.25 is for polynomials over a field; the brief's reading
--   - encoding: poly(·) and O(1) → C·(sum of the arguments)^C with one universal C, and one universal depth bound; reason: the paper defines poly(a_1,…,a_k) as (a_1+⋯+a_k)^c for an absolute constant c (p. 15)
--   - encoding: β "a root of F(0, Y)" → β in any field L ⊇ F, with rootMultiplicity e ≥ 1; reason: roots live in an extension
-- source:
--   Bhattacharjee, Kothary, Rai, Saraf, Deterministic Algorithms for Low Individual Degree Factors of Sparse Polynomials, arXiv:2606.27293 (held version, sha256 9837a932…), p. 25, Theorem 2.28 (with the definition of R_e, p. 24)

import Mathlib
import Definitions.Def_SetMultCost_Circuit
import Definitions.Def_SparseLowFactors_BoundedDeg_Sparse
import Definitions.Def_SparseLowFactors_BoundedDeg_Sylvester
import Definitions.Def_SparseLowFactors_BoundedDeg_PowerSeriesRoots
import Definitions.Def_SparseLowFactors_BoundedDeg_Circuits

open SetMultCost

namespace SparseLowFactors.BoundedDeg

theorem theorem_2_28 :
    ∃ C c₀ : ℕ,
    ∀ (F : Type) [Field F] (n d D e s' Δ : ℕ) (G : Polynomial (Polynomial (MvPolynomial (Fin n) F))),
      (ringChar F = 0 ∨ d < ringChar F) →
      G.Monic → G.natDegree = d → degT G = D →
      (∀ i, ∃ a : F, (G.coeff i).coeff 0 = MvPolynomial.C a) →
      HenselReady (G.map (Polynomial.mapRingHom
          (algebraMap (MvPolynomial (Fin n) F) (FractionRing (MvPolynomial (Fin n) F)))))
        (Polynomial.evalRingHom 0) →
      ∀ Γ : Circuit (Fin n ⊕ Fin 2) F, Γ.size ≤ s' → depth Γ ≤ Δ → Γ.value = toMvXTY G →
      ∀ (L : Type) [Field L] [Algebra F L] (β : L),
        1 ≤ e →
        (((atTZero G).map MvPolynomial.constantCoeff).map (algebraMap F L)).rootMultiplicity β = e →
        ∃ (A : MvPolynomial (Fin n ⊕ Fin 2) F) (B : Polynomial F)
          (ΓA ΓB : Circuit (Fin n ⊕ Fin 2) F),
          B ≠ 0 ∧
          Rgen embXT
              (algebraMap (MvPolynomial (Fin n ⊕ Fin 2) F) (FractionRing (MvPolynomial (Fin n ⊕ Fin 2) F))
                (MvPolynomial.X (Sum.inr 1))) e D G =
            algebraMap (MvPolynomial (Fin n ⊕ Fin 2) F)
                (FractionRing (MvPolynomial (Fin n ⊕ Fin 2) F)) A /
              algebraMap (MvPolynomial (Fin n ⊕ Fin 2) F)
                (FractionRing (MvPolynomial (Fin n ⊕ Fin 2) F))
                (Polynomial.aeval (MvPolynomial.X (Sum.inr 1)) B) ∧
          ΓA.value = A ∧ ΓB.value = Polynomial.aeval (MvPolynomial.X (Sum.inr 1)) B ∧
          ΓA.size ≤ C * (n + s' + d + D) ^ C ∧ ΓB.size ≤ C * (n + s' + d + D) ^ C ∧
          depth ΓA ≤ Δ + c₀ ∧ depth ΓB ≤ Δ + c₀ ∧
          Polynomial.aeval β B ≠ 0 ∧
          PowerSeries.trunc (D + 1) (psRootT G L β) =
            polyTrunc (D + 1)
              (Rgen (Polynomial.mapRingHom (MvPolynomial.map (algebraMap F L)))
                (Polynomial.C (MvPolynomial.C β)) e D G) := by sorry

end SparseLowFactors.BoundedDeg
