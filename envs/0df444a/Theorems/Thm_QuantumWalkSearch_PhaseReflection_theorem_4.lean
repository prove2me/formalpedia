-- Prove2me | Theorems.Thm_QuantumWalkSearch_PhaseReflection_theorem_4
-- name    : QuantumWalkSearch.PhaseReflection.theorem_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T08:45:44.860626+00:00
-- url     : https://prove2.me/theorems/dc302c04-2c0d-473a-ad2c-cd9dde30a005
-- title:
--   Theorem 4 (Szegedy) — the spectrum of $W(P)$ on $\mathcal A+\mathcal B$ is given by the singular values of $D(P)$
-- statement:
--   Let $P$ be an irreducible Markov chain on a finite set $X$ with stationary distribution $\pi$, let $W(P)=\mathrm{ref}(\mathcal B)\cdot\mathrm{ref}(\mathcal A)$ be its quantum walk on $\mathcal H=\mathbb C^{X\times X}$, and $D(P)$ its discriminant matrix. Then:
--
--   1. For every $\theta\in(0,\pi/2)$, the eigenvalues $e^{2i\theta}$ and $e^{-2i\theta}$ of $W(P)$ on $\mathcal A+\mathcal B$ each have multiplicity equal to the multiplicity of $\cos\theta$ as a singular value of $D(P)$:
--   $$\dim\big(\ker(W(P)-e^{\pm2i\theta})\cap(\mathcal A+\mathcal B)\big)=\#\{j : \sigma_j(D(P))=\cos\theta\}.$$
--   2. $W(P)$ acts as the identity on $\mathcal A\cap\mathcal B$, and $\mathcal A\cap\mathcal B$ is the image of the left singular vectors of $D(P)$ with singular value $1$ under $u\mapsto\sum_x u_x|x\rangle|p_x\rangle$, and also the image of the right singular vectors with singular value $1$ under $v\mapsto\sum_y v_y|p^*_y\rangle|y\rangle$.
--   3. $W(P)$ acts as $-\mathrm{Id}$ on $\mathcal A\cap\mathcal B^\perp$ and on $\mathcal A^\perp\cap\mathcal B$; $\mathcal A\cap\mathcal B^\perp$ (resp. $\mathcal A^\perp\cap\mathcal B$) is the image of the left (resp. right) singular vectors with singular value $0$.
--   4. $W(P)$ has no other eigenvalues on $\mathcal A+\mathcal B$: an eigenvalue with an eigenvector in $\mathcal A+\mathcal B$ is $1$, $-1$, or $e^{\pm2i\theta}$ with $\theta\in(0,\pi/2)$ and $\cos\theta$ a singular value of $D(P)$; the $1$-eigenvectors in $\mathcal A+\mathcal B$ form exactly $\mathcal A\cap\mathcal B$ and the $(-1)$-eigenvectors form exactly $(\mathcal A\cap\mathcal B^\perp)+(\mathcal A^\perp\cap\mathcal B)$. On $\mathcal A^\perp\cap\mathcal B^\perp$, $W(P)$ acts as $\mathrm{Id}$.
--
--   This theorem translates the singular value decomposition of $D(P)$ into the spectral decomposition of $W(P)$; it is a variant of Jordan's lemma on two subspaces, and it is what lets phase estimation on $W(P)$ distinguish $|\pi\rangle$ from the rest of $\mathcal A+\mathcal B$.
--
--   **Formalization Note** "Spanned by the left (right) singular vectors with singular value $c$" is rendered as the image under the embedding into $\mathcal A$ (resp. $\mathcal B$) of the complex kernel of $DD^{\mathsf T}-c^2$ (resp. $D^{\mathsf T}D-c^2$). Multiplicity in part 1 is the dimension of the eigenspace intersected with $\mathcal A+\mathcal B$ (which is $W(P)$-invariant), so "with the same multiplicity" is stated for every $\theta\in(0,\pi/2)$ and both signs; "exactly" in part 1 is the case where the multiplicity is $0$. "No other eigenvalues" (part 4) is stated as the list of possible eigenvalues together with the identification of the $\pm1$-eigenspaces.
-- source:
--   Magniez, Nayak, Roland, Santha, Search via Quantum Walk, arXiv:quant-ph/0608026v4, p. 7, Theorem 4 (Szegedy [29]), parts 1–4

import Mathlib
import Definitions.Def_QuantumWalkSearch_PhaseReflection_Walk

namespace QuantumWalkSearch.PhaseReflection

/-- Theorem 4 (Szegedy), p. 7, parts 1–4, for an irreducible chain `P` with stationary
distribution `π`. Part 1: for `θ ∈ (0, π/2)` the eigenvalues `e^{±2iθ}` of `W(P)` on `A + B` have
multiplicity equal to the multiplicity of `cos θ` as a singular value of `D(P)`. Part 2: `W(P)` is
the identity on `A ∩ B`, which is the image in `A` of the left, and the image in `B` of the
right, singular vectors with singular value `1`. Part 3: `W(P) = −Id` on `A ∩ B⊥` and on
`A⊥ ∩ B`, which are the images of the left (resp. right) singular vectors with singular value `0`.
Part 4: no other eigenvalues on `A + B` (the `1`- and `−1`-eigenspaces on `A + B` are exactly the
subspaces of parts 2 and 3); `W(P) = Id` on `A⊥ ∩ B⊥`. -/
theorem theorem_4 {X : Type*} [Fintype X] [DecidableEq X] (P : Matrix X X ℝ) (πd : X → ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ X) (hirr : P.IsIrreducible)
    (hπ : IsStationaryDist P πd) :
    -- Part 1
    (∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      Module.finrank ℂ ↥(Module.End.eigenspace (walk P πd)
          (Complex.exp (2 * (θ : ℂ) * Complex.I)) ⊓ (spaceA P ⊔ spaceB P πd)) =
        singularValueMult P πd (Real.cos θ) ∧
      Module.finrank ℂ ↥(Module.End.eigenspace (walk P πd)
          (Complex.exp (-(2 * (θ : ℂ) * Complex.I))) ⊓ (spaceA P ⊔ spaceB P πd)) =
        singularValueMult P πd (Real.cos θ)) ∧
    -- Part 2
    (∀ v ∈ spaceA P ⊓ spaceB P πd, walk P πd v = v) ∧
    spaceA P ⊓ spaceB P πd = leftSingularImage P πd 1 ∧
    spaceA P ⊓ spaceB P πd = rightSingularImage P πd 1 ∧
    -- Part 3
    (∀ v ∈ spaceA P ⊓ (spaceB P πd)ᗮ, walk P πd v = -v) ∧
    (∀ v ∈ (spaceA P)ᗮ ⊓ spaceB P πd, walk P πd v = -v) ∧
    spaceA P ⊓ (spaceB P πd)ᗮ = leftSingularImage P πd 0 ∧
    (spaceA P)ᗮ ⊓ spaceB P πd = rightSingularImage P πd 0 ∧
    -- Part 4
    (∀ μ : ℂ, Module.End.eigenspace (walk P πd) μ ⊓ (spaceA P ⊔ spaceB P πd) ≠ ⊥ →
      μ = 1 ∨ μ = -1 ∨ ∃ θ ∈ Set.Ioo 0 (Real.pi / 2), IsSingularValue P πd (Real.cos θ) ∧
        (μ = Complex.exp (2 * (θ : ℂ) * Complex.I) ∨
          μ = Complex.exp (-(2 * (θ : ℂ) * Complex.I)))) ∧
    Module.End.eigenspace (walk P πd) 1 ⊓ (spaceA P ⊔ spaceB P πd) = spaceA P ⊓ spaceB P πd ∧
    Module.End.eigenspace (walk P πd) (-1) ⊓ (spaceA P ⊔ spaceB P πd) =
      spaceA P ⊓ (spaceB P πd)ᗮ ⊔ (spaceA P)ᗮ ⊓ spaceB P πd ∧
    (∀ v ∈ (spaceA P)ᗮ ⊓ (spaceB P πd)ᗮ, walk P πd v = v) := by sorry

end QuantumWalkSearch.PhaseReflection
