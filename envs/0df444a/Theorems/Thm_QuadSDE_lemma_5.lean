-- Prove2me | Theorems.Thm_QuadSDE_lemma_5
-- name    : QuadSDE.lemma_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:16:55.976809+00:00
-- url     : https://prove2.me/theorems/21b36708-d37f-465b-881d-77b9e5be3b52
-- title:
--   Lemma 5 — $C_0$ represents $-f\cdot\nabla$, is skew, couples adjacent degrees, $\|Q_{n+1}C_0Q_n\|\le J\sqrt r\,n\sqrt{n+1}$
-- statement:
--   Let the drift be admissible, with strength at most $J$ and at most $r$ channels, and let $C_0=\sum_{i,j,k}c_{ijk}(a_i^\dagger a_ja_k-a_k^\dagger a_j^\dagger a_i)$ act on the Fock space, where a polynomial $u$ is identified with the vector $\hat u$ of its Hermite coefficients $\hat u_{\mathbf m}=\langle H_{\mathbf m},u\rangle_\mu$. Then:
--   1. ($C_0$ represents $-f\cdot\nabla$) for every polynomial $\varphi$, the Hermite coefficient vector of $-f\cdot\nabla\varphi$ is $C_0\hat\varphi$;
--   2. (skew-symmetry) $\langle u,C_0v\rangle=-\langle C_0u,v\rangle$ for all finite Hermite vectors $u,v$;
--   3. (adjacent degrees) $Q_nC_0Q_{n'}=0$ whenever $|n-n'|\ne1$;
--   4. (vacuum) $C_0|0\rangle=0$;
--   5. for every $n\ge1$ and every vector $v$,
--   $$\|Q_{n+1}C_0Q_nv\|\le J\sqrt r\,n\sqrt{n+1}\,\|Q_nv\|\qquad(33);$$
--   6. ($K(t)^\dagger$ represents $G_t$) for all $p,q,t$ and every polynomial $\varphi$, the Hermite coefficient vector of $G_t\varphi$ is
--   $$K(t)^\dagger\hat\varphi=\big(-\lambda(t)M-\sqrt{\rho(t)}\,C_0\big)\hat\varphi.$$
--
--   These properties make the evolution of the Hermite coefficients a linear ODE $\psi'=K(t)\psi$ whose couplings grow only like $n^{3/2}$ between adjacent degrees.
--
--   Differences from the source:
--   - reading: C₀ represents −f · ∇ on polynomials; K(t)† represents G_t on finite Hermite vectors → equality of Hermite coefficient vectors: coeff(−f·∇φ) = C₀ φ̂ and coeff(G_t φ) = (−λ(t)M − √ρ(t) C₀) φ̂ for every real polynomial φ; reason: this is what representing an operator on the basis |m⟩ ↔ H_m means; K(t)† = −λM − √ρ C₀ since M† = M and C₀† = −C₀
--   - reading: skew-symmetric; couples only adjacent degrees; annihilates the vacuum; ‖Q_{n+1}C₀Q_n‖ ≤ J√r n√(n+1) → ⟨u, C₀v⟩ = −⟨C₀u, v⟩ for finitely supported u, v; Q_n C₀ Q_{n'} = 0 for |n − n'| ≠ 1; C₀|0⟩ = 0; ‖Q_{n+1}C₀Q_n v‖ ≤ J√r n√(n+1) ‖Q_n v‖ for every v; reason: operator-norm bound on a finite-dimensional degree space is the bound for all vectors
--   - generalization: clause 6 at the parameters of the problem → clause 6 for all real p, q, t; reason: it is an algebraic identity; the source's parameters are a special case
--   - encoding: operators on 𝓕 and on finite Hermite vectors → operators acting coefficientwise on functions ℤ_{≥0}^N → ℂ; Hermite coefficients real, embedded in ℂ; reason: same values on the vectors the lemma concerns
-- source:
--   Bravyi, Byrne, Zayats, Zhuk, Zlokapa, Quantum algorithms for stochastic nonlinear differential equations, arXiv:2606.08349 (sha256 29bd9b01…94cdf), §4.2, Lemma 5, p. 19

import Mathlib
import Definitions.Def_QuadSDE_DriftClass
import Definitions.Def_QuadSDE_Frame
import Definitions.Def_QuadSDE_GaussHermite
import Definitions.Def_QuadSDE_Generator
import Definitions.Def_QuadSDE_Fock

namespace QuadSDE

/-- **Lemma 5 (the Kolmogorian).**
Bravyi–Byrne–Zayats–Zhuk–Zlokapa, arXiv:2606.08349 (sha256 29bd9b01…), §4.2, Lemma 5, p. 19: "The
operator `C₀` represents `−f · ∇` on polynomials and is skew-symmetric. It couples only adjacent
degrees, annihilates the vacuum, and satisfies `‖Q_{n+1}C₀Q_n‖ ≤ J√r n√(n + 1)`, `n ≥ 1`. (33) In
particular, `K(t)†` represents `G_t` from Eq. (31) on finite Hermite vectors."

Let the drift be admissible, with strength at most `J` and at most `r` channels, and let
`C₀ = Σ_{i,j,k} c_{ijk}(a_i† a_j a_k − a_k† a_j† a_i)` (Eq. (32)). Identify a polynomial `u` with
the vector `û` of its Hermite coefficients `û_m = ⟨H_m, u⟩_µ`. Then:
1. for every polynomial `φ`, the Hermite coefficient vector of `−f · ∇φ` is `C₀ φ̂`;
2. `⟨u, C₀ v⟩ = −⟨C₀ u, v⟩` for all finite Hermite vectors `u, v`;
3. `Q_n C₀ Q_{n'} = 0` whenever `|n − n'| ≠ 1`;
4. `C₀ |0⟩ = 0`;
5. for `n ≥ 1` and every `v`, `‖Q_{n+1} C₀ Q_n v‖ ≤ J √r n √(n + 1) ‖Q_n v‖`;
6. for all `p, q, t` and every polynomial `φ`, the Hermite coefficient vector of `G_t φ` is
   `K(t)† φ̂ = (−λ(t) M − √ρ(t) C₀) φ̂`.

**Formalization Note.** Vectors are coefficient functions on multi-indices; the operators act
coefficientwise. Finite Hermite vectors are finitely supported functions. The Hermite coefficients
of a polynomial are real and are embedded in `ℂ`. In clause 6, `K(t)† = −λ(t)M − √ρ(t)C₀` is the
adjoint of `K(t) = −λ(t)M + √ρ(t)C₀`, since `M† = M` and (clause 2) `C₀† = −C₀`; it is written out
explicitly. -/
theorem lemma_5 {N : ℕ} (c : Coeff N) (hc : IsAdmissibleDrift c) (J : ℝ) (hJ : strengthLE c J)
    (r : ℕ) (hr : channelsLE c r) :
    (∀ (φ : MvPolynomial (Fin N) ℝ) (m : MIdx N),
        ((hermiteCoeff (fun x => -MvPolynomial.eval x (driftDeriv c φ)) m : ℝ) : ℂ) =
          C0 c (fun m' => ((hermiteCoeff (fun x => MvPolynomial.eval x φ) m' : ℝ) : ℂ)) m) ∧
    (∀ u v : MIdx N →₀ ℂ, fockInner (⇑u) (C0 c ⇑v) = -fockInner (C0 c ⇑u) ⇑v) ∧
    (∀ n n' : ℕ, n ≠ n' + 1 → n' ≠ n + 1 → ∀ v : MIdx N → ℂ, Qdeg n (C0 c (Qdeg n' v)) = 0) ∧
    C0 c (vacuum N) = 0 ∧
    (∀ n : ℕ, 1 ≤ n → ∀ v : MIdx N → ℂ,
        Real.sqrt (degNormSq (n + 1) (C0 c (Qdeg n v))) ≤
          J * Real.sqrt r * n * Real.sqrt ((n : ℝ) + 1) * Real.sqrt (degNormSq n v)) ∧
    ∀ (p q t : ℝ) (φ : MvPolynomial (Fin N) ℝ) (m : MIdx N),
      ((hermiteCoeff (fun x => MvPolynomial.eval x (genPoly c p q t φ)) m : ℝ) : ℂ) =
        -((lam p q t : ℝ) : ℂ) *
            numOp (fun m' => ((hermiteCoeff (fun x => MvPolynomial.eval x φ) m' : ℝ) : ℂ)) m -
          ((Real.sqrt (rho p q t) : ℝ) : ℂ) *
            C0 c (fun m' => ((hermiteCoeff (fun x => MvPolynomial.eval x φ) m' : ℝ) : ℂ)) m := by sorry

end QuadSDE
