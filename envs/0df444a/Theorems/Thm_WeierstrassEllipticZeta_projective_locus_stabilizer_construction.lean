-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_projective_locus_stabilizer_construction
-- name    : WeierstrassEllipticZeta.projective_locus_stabilizer_construction
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-20T06:08:35.91916+00:00
-- url     : https://prove2.me/theorems/627b69df-d349-4518-a8eb-f2e316767504
-- title:
--   Canonical proper subgroup from a locus in a projective hypersurface
-- statement:
--   Fix a complex period pair $L$ with lattice $\Lambda$, its canonical Weierstrass functions, normalized entire sigma differential data, and five entire functions with no common zero satisfying
--
--   $$
--   S(z)=\sigma(z)^3\bigl(1,\wp(z),\wp'(z),\zeta(z),
--   \wp'(z)\zeta(z)+2\wp(z)^2\bigr)\qquad(z\notin\Lambda).
--   $$
--
--   Let $\eta:\Lambda\to\mathbb C$ be integer-linear. Let $Q$ be a polynomial homogeneous of degree $n\ge0$ in its last five variables, and define its covering-space evaluation by
--
--   $$
--   \mathcal F_Q(t,z,u)=Q\bigl(1,t,S_0(z),S_1(z),S_2(z),
--   S_3(z)+uS_0(z),S_4(z)+uS_2(z)\bigr).
--   $$
--
--   Assume $z\mapsto\mathcal F_Q(z,z,0)$ is not identically zero. Let $W\subseteq\mathbb C^3$ be nonempty and suppose $\mathcal F_Q(w)=0$ for every $w\in W$. Define
--
--   $$
--   V_W=\{v:\ w+tv\in W\text{ for every }t\in\mathbb C,\ w\in W\},
--   \quad H_W=\{(v_0,[(v_1,v_2)]):v\in V_W\}\subseteq G,
--   $$
--
--   where
--
--   $$
--   G=\mathbb C\times\bigl(\mathbb C^2/\{(\omega,-\eta(\omega)):\omega\in\Lambda\}\bigr).
--   $$
--
--   Then the following hold:
--
--   1. The displayed formula for $H_W$ is its exact membership characterization. For every complex linear subspace $U\subseteq\mathbb C^3$,
--
--   $$
--   U\subseteq V_W\quad\Longleftrightarrow\quad w+U\subseteq W\text{ for every }w\in W.
--   $$
--
--   2. There is $r\in W$ such that $\mathcal F_Q(r+v)=0$ for every $v\in V_W$.
--
--   3. The subgroup is proper, $H_W\ne G$. There is $a\in\{0,1\}$ such that, for every real $m$,
--
--   $$
--   m^a=\begin{cases}m&v_0=0\text{ for every }v\in V_W,\\1&\text{otherwise},\end{cases}
--   $$
--
--   and either $a=1$ and $H_W\subseteq\ker\pi_a$, or $a=0$ and $H_W\subseteq\ker\pi_E$. Here $\pi_a(t,[(z,u)])=t$ and $\pi_E(t,[(z,u)])=[z]\in\mathbb C/\Lambda$.
--
--   This constructs a candidate subgroup and its parametrization from a chosen locus, and proves its translated containment and projection profile. It does not choose a locus satisfying a uniform multiplicity bound or prove that the subgroup is algebraic. When the construction is applied to the mission, $\eta$ is the actual quasiperiod map.
--
--   **Formalization Note.** This is the analytic-coordinate counterpart of the stabilizer construction in [Philippon (1986), §5, pp. 380–381](https://www.numdam.org/item/10.24033/bsmf.2060.pdf), combined with the proved subgroup restrictions for the particular group in [Senthil Kumar (2026), Appendix A, §A.2](https://doi.org/10.1017/S001309152610145X).
-- source:
--   Philippon (1986), Lemmes de zeros dans les groupes algebriques commutatifs, Bull. Soc. Math. France 114, 355-383, section 5, Lemma 5.1, pp. 380-382. https://www.numdam.org/item/10.24033/bsmf.2060.pdf. Senthil Kumar K (2026), Appendix A, Theorem A.2 and section A.2. https://doi.org/10.1017/S001309152610145X. Specialized covering-space translation-direction construction; no algebraic-stabilizer identification is assumed. Uniform locus selection and its multiplicity bound remain open.

import Definitions.Def_TranscendenceTheory_LinearTranslationStabilizer
import Definitions.Def_WeierstrassEllipticZeta_SigmaDifferential
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Algebra.MvPolynomial.Eval
open WeierstrassEllipticZeta TranscendenceTheory MvPolynomial
open scoped Classical

theorem WeierstrassEllipticZeta.projective_locus_stabilizer_construction
    (L : PeriodPair) (D : EllipticSigmaDifferentialData L)
    (S : Fin 5 → ℂ → ℂ)
    (hS : ∀ j, AnalyticOnNhd ℂ (S j) Set.univ)
    (hS_value : ∀ z : ℂ, z ∉ L.lattice → ∀ j : Fin 5,
      S j z = D.sigma z ^ 3 * ![1, L.weierstrassP z, L.derivWeierstrassP z,
        weierstrassZeta L z,
        L.derivWeierstrassP z * weierstrassZeta L z + 2 * L.weierstrassP z ^ 2] j)
    (hS_ne : ∀ z : ℂ, ∃ j : Fin 5, S j z ≠ 0)
    (η : L.lattice →ₗ[ℤ] ℂ)
    (Q : MvPolynomial (Fin 7) ℂ) (n : ℕ)
    (hQ : ∀ d ∈ Q.support, d 2 + d 3 + d 4 + d 5 + d 6 = n)
    (hne : (fun z : ℂ => eval
      ![1, z, S 0 z, S 1 z, S 2 z, S 3 z, S 4 z] Q) ≠ 0)
    (W : Set (Fin 3 → ℂ)) (hW : W.Nonempty)
    (hWQ : ∀ w ∈ W,
      eval ![1, w 0, S 0 (w 1), S 1 (w 1), S 2 (w 1),
        S 3 (w 1) + w 2 * S 0 (w 1), S 4 (w 1) + w 2 * S 2 (w 1)] Q = 0) :
    let V := linearTranslationDirections W
    let H := linearTranslationImage L.lattice η W
    (∀ g, g ∈ H ↔ ∃ v ∈ V,
      g = (v 0, (extensionPeriodGraph L.lattice η).mkQ (v 1, v 2))) ∧
    (∀ U : Submodule ℂ (Fin 3 → ℂ), U ≤ V ↔ ∀ w ∈ W, ∀ v ∈ U, w + v ∈ W) ∧
    ∃ r ∈ W,
      (∀ v ∈ V,
        eval ![1, r 0 + v 0, S 0 (r 1 + v 1), S 1 (r 1 + v 1), S 2 (r 1 + v 1),
          S 3 (r 1 + v 1) + (r 2 + v 2) * S 0 (r 1 + v 1),
          S 4 (r 1 + v 1) + (r 2 + v 2) * S 2 (r 1 + v 1)] Q = 0) ∧
      H ≠ ⊤ ∧ ∃ a : ℕ,
        (∀ m : ℝ, m ^ a = if (∀ v ∈ V, v 0 = 0) then m else 1) ∧
        ((a = 1 ∧ H ≤ LinearMap.ker (extensionAdditiveProjection L.lattice η)) ∨
          (a = 0 ∧ H ≤ LinearMap.ker (extensionEllipticProjection L.lattice η))) := by sorry
