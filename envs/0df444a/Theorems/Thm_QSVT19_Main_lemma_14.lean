-- Prove2me | Theorems.Thm_QSVT19_Main_lemma_14
-- name    : QSVT19.Main.lemma_14
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T17:28:38.774811+00:00
-- url     : https://prove2.me/theorems/b67e6255-8543-414a-8e96-43a70a05f464
-- title:
--   Lemma 14: invariant subspace decomposition of a projected unitary
-- statement:
--   Let $U$ be unitary, $\Pi,\widetilde\Pi$ orthogonal projectors, and fix a singular value decomposition of $\widetilde\Pi U\Pi$ with the vectors $\psi_i^\perp,\tilde\psi_i^\perp$ of Definition 12. Then:
--   1. if $\varsigma_i=1$, then $U|\psi_i\rangle=|\tilde\psi_i\rangle$;
--   2. if $0<\varsigma_i<1$, then
--   $$U|\psi_i\rangle=\varsigma_i|\tilde\psi_i\rangle+\sqrt{1-\varsigma_i^2}\,|\tilde\psi_i^\perp\rangle,\qquad U|\psi_i^\perp\rangle=\sqrt{1-\varsigma_i^2}\,|\tilde\psi_i\rangle-\varsigma_i|\tilde\psi_i^\perp\rangle;$$
--   3. a vector $v$ is orthogonal to all of $\psi_i$, $\psi_i^\perp$, $U^\dagger\tilde\psi_j$ ($\varsigma_j=0$) if and only if $Uv$ is orthogonal to all of $\tilde\psi_j$, $\tilde\psi_i^\perp$, $U\psi_j$ ($\varsigma_j=0$), i.e. $U$ maps $\mathcal H_\perp$ onto $\widetilde{\mathcal H}_\perp$;
--   4. $\Pi|\psi_i^\perp\rangle=0$ and $\widetilde\Pi|\tilde\psi_i^\perp\rangle=0$ when $0<\varsigma_i<1$;
--   5. $\Pi U^\dagger|\tilde\psi_j\rangle=0$ when $\varsigma_j=0$ ($j\in[\tilde d]$), and $\widetilde\Pi U|\psi_j\rangle=0$ when $\varsigma_j=0$ ($j\in[d]$).
--
--   Items 1–3 are the block decomposition (24) of $U$ into one- and two-dimensional pieces; items 4–5 are the nontrivial entries of (25) and (27). This "qubitization" reduces the analysis of $U_\Phi$ to $2\times2$ blocks.
--
--   **Formalization Note** The block notation of Definition 13 is rendered as vector equations. The trivial $[1]$ blocks on $\mathcal H^R_i,\mathcal H^L_i$ and the phase forms (26), (28) are not restated. The printed index set $[d]\setminus[r]$ of the $\mathcal H^L$ blocks in (25)–(28) is read as $[\tilde d]\setminus[r]$, as in (24).
-- source:
--   Gilyén, Su, Low, Wiebe, arXiv:1806.01838v1, p. 17, Lemma 14, (24)–(25), (27), proof (29)–(30)

import Definitions.Def_QSVT19_Main_Setting

set_option autoImplicit false

open scoped ComplexOrder
open Polynomial Matrix

namespace QSVT19.Main

/-- Gilyén, Su, Low, Wiebe, arXiv:1806.01838v1, Lemma 14, p. 17: "Let H_U be a finite-dimensional Hilbert-space and U, Π, Π̃ ∈ End(H_U) be
as in Definition 11. Then using the singular value decomposition of Definition 12 we have that
U = ⊕_{i∈[k]} [ς_i]^{H_i}_{H̃_i} ⊕ ⊕_{i∈[r]\[k]} [ς_i √(1 − ς_i^2); √(1 − ς_i^2) −ς_i]^{H_i}_{H̃_i}
⊕ ⊕_{i∈[d]\[r]} [1]^{H^R_i}_{H̃^R_i} ⊕ ⊕_{i∈[d̃]\[r]} [1]^{H^L_i}_{H̃^L_i} ⊕ [·]^{H_⊥}_{H̃_⊥}. (24)
Moreover," (25)–(28) describe `2Π − I`, `2Π̃ − I` and their phases on the same subspaces.

**Formalization Note.** `H_U` is `ι → ℂ` for a finite type `ι`, with inner product
`star v ⬝ᵥ w`; `Π, Π̃` are `Proj, Projt`; "unitary" is `U ∈ Matrix.unitaryGroup ι ℂ` and
"orthogonal projector" is `IsStarProjection` (self-adjoint idempotent). The block notation `[·]^H_{H′}` of Definition 13 (matrices in the spanning bases of
Definition 12) is rendered by vector equations, which is what the proof's (29)–(30) establish:
1. `[ς_i]` for `ς_i = 1` (`i ∈ [k]`): `U|ψ_i⟩ = |ψ̃_i⟩`;
2. the 2×2 block for `0 < ς_i < 1` (`i ∈ [r] \ [k]`): `U|ψ_i⟩ = ς_i|ψ̃_i⟩ + √(1−ς_i²)|ψ̃_i^⊥⟩` and
   `U|ψ_i^⊥⟩ = √(1−ς_i²)|ψ̃_i⟩ − ς_i|ψ̃_i^⊥⟩`;
3. `[·]^{H_⊥}_{H̃_⊥}`: `U` maps `H_⊥` onto `H̃_⊥`, i.e. `v` is orthogonal to every spanning vector
   of Definition 12 iff `Uv` is orthogonal to every tilde spanning vector.
The blocks `[1]^{H^R_i}_{H̃^R_i}` and `[1]^{H^L_i}_{H̃^L_i}` hold by the choice of bases
(`H̃^R_i = Span(U|ψ_i⟩)`, `H^L_i = Span(U^†|ψ̃_i⟩)`) and are not restated. Of (25) and (27) the
non-definitional entries are stated: `Π|ψ_i^⊥⟩ = 0`, `Π̃|ψ̃_i^⊥⟩ = 0`, `ΠU^†|ψ̃_j⟩ = 0` on `H^L` and
`Π̃U|ψ_j⟩ = 0` on `H̃^R` (the `+1` entries are `Π|ψ_i⟩ = |ψ_i⟩`, immediate from Definition 11);
(26) and (28) follow from (25), (27) and the definition of `e^{iφ(2Π−I)}` and are not restated.
The printed index set `[d] \ [r]` of the `H^L` blocks in (25)–(28) is read as `[d̃] \ [r]`, as in
(24). Index sets are the predicates of `orthoFamily` (`ς` extended by zero). -/
theorem lemma_14 {ι : Type*} [Fintype ι] [DecidableEq ι] (U Proj Projt : Matrix ι ι ℂ) (hU : U ∈ Matrix.unitaryGroup ι ℂ) (hProj : IsStarProjection Proj) (hProjt : IsStarProjection Projt) (S : ProjUnitarySVD U Proj Projt) :
    (∀ i, S.ς i = 1 → U *ᵥ S.ψmin i = S.ψtmin i) ∧ (∀ i, 0 < S.ς i → S.ς i < 1 → U *ᵥ S.ψmin i = (S.ς i : ℂ) • S.ψtmin i + (Real.sqrt (1 - S.ς i ^ 2) : ℂ) • S.ψtperp i ∧ U *ᵥ S.ψperp i = (Real.sqrt (1 - S.ς i ^ 2) : ℂ) • S.ψtmin i - (S.ς i : ℂ) • S.ψtperp i) ∧ (∀ v : ι → ℂ, (∀ a, star (S.orthoFamily a) ⬝ᵥ v = 0) ↔ (∀ b, star (S.orthoFamilyTilde b) ⬝ᵥ (U *ᵥ v) = 0)) ∧ (∀ i, 0 < S.ς i → S.ς i < 1 → Proj *ᵥ S.ψperp i = 0 ∧ Projt *ᵥ S.ψtperp i = 0) ∧ (∀ j : Fin S.dt, S.ςextT j = 0 → Proj *ᵥ (Uᴴ *ᵥ S.ψt j) = 0) ∧ (∀ j : Fin S.d, S.ςext j = 0 → Projt *ᵥ (U *ᵥ S.ψ j) = 0) := by sorry

end QSVT19.Main
