-- Prove2me | Theorems.Thm_ShadowBootstrap_lemma_5_9
-- name    : ShadowBootstrap.lemma_5_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:24:15.456608+00:00
-- url     : https://prove2.me/theorems/a51a6bde-07a5-4ffe-9670-291c932a41d7
-- title:
--   Lemma 5.9 (with Corollary 5.10) — $\mathbb E[\hat o] = p_x\mathrm{Tr}(O\psi_x)$ and $\mathrm{Var}[\hat o] \le \frac{C\|O\|_F^2}{N_\ell}(p_x^2 + \frac{p_x}{S_\ell})$
-- statement:
--   Fix a level $\ell$, a node $x \in \{0,1\}^\ell$ and a suffix ensemble $E$ on $n - \ell$ qubits that is Clifford, has invertible shadow channel and satisfies Eq. (8) with constant $C_F$ for every state; let $C = C_F + 1$. Let $|\psi\rangle$ be a unit vector, $\varphi_x = (\langle x|\otimes I)|\psi\rangle$, $p_x = \|\varphi_x\|_2^2$ and $N_\ell, S_\ell \ge 1$. For every suffix observable $O$, the conditional estimator $\hat o$ of Eq. (20) satisfies
--   $$\mathbb E[\hat o] = p_x\operatorname{Tr}(O\psi_x)\qquad\text{and}\qquad \mathbb E\big[|\hat o - p_x\operatorname{Tr}(O\psi_x)|^2\big] \le \frac{C\|O\|_F^2}{N_\ell}\Big(p_x^2 + \frac{p_x}{S_\ell}\Big).$$
--   For Hermitian $O$ the estimator is real and the second bound is $\mathrm{Var}[\hat o] \le \frac{C\|O\|_F^2}{N_\ell}(p_x^2 + \frac{p_x}{S_\ell})$, the statement of Lemma 5.9; for general $O$ it is Corollary 5.10.
--
--   These bounds feed the estimate of the reconstruction matrix $\hat B_x$ (Lemma 5.12).
--
--   Differences from the source:
--   - reading: the suffix ensemble of Lemma 5.4 with the constant of Lemma 3.8 → any finite Clifford ensemble with invertible shadow channel satisfying Eq. (8) with C_F for every state; reason: these are the measurement assumptions of §5.2
--   - generalization: C (unspecified) → the explicit C = C_F + 1; reason: the variance decomposition has a p_x(1−p_x)Tr(Oψ_x)²/S_ℓ term bounded by ‖O‖_F², which needs the +1; explicit constants specialize
--   - generalization: Hermitian O, Var[ô] → every complex O, E|ô − p_xTr(Oψ_x)|² (Corollary 5.10); reason: for Hermitian O the estimator is real with mean p_xTr(Oψ_x), so this is the variance
--   - encoding: p_xTr(Oψ_x) with ψ_x = φ_x/√p_x → Tr(Oφ_xφ_x†); reason: equal when p_x > 0 and defined when p_x = 0
-- source:
--   Cho, Kim, Shadow bootstrapping: Nearly minimal-setting pure-state tomography with shallow Clifford measurements, arXiv:2611.06073 (version of November 2, 2026, sha256 34fab758…), Lemma 5.9, p.19, and Corollary 5.10, pp.20 and 33

import Mathlib
import Definitions.Def_ShadowBootstrap_condEst
import Definitions.Def_ShallowShadows_ShadowNorm_IsCliffordPrimitive

open ClassicalShadow.Linear ShallowShadows.ShadowNorm

namespace ShadowBootstrap

/-- Cho, Kim, *Shadow bootstrapping: Nearly minimal-setting pure-state tomography with shallow
Clifford measurements*, arXiv:2611.06073 (version of November 2, 2026, sha256 34fab758…),
Lemma 5.9, p.19, with Corollary 5.10, pp.20 and 33: fix `x ∈ {0,1}^ℓ`. For any Hermitian
observable `O` on the suffix, the estimator of Eq. (20) satisfies `E[ô] = p_x Tr(Oψ_x)` and
`Var[ô] ≤ (C‖O‖_F²/N_ℓ)(p_x² + p_x/S_ℓ)`; for any (complex) suffix observable `O`,
`E[|ô − p_x Tr(Oψ_x)|²] ≤ (C‖O‖_F²/N_ℓ)(p_x² + p_x/S_ℓ)`.

**Formalization Note** The suffix has `j = n − ℓ` qubits and its ensemble `E` is any finite
Clifford ensemble with invertible shadow channel satisfying Eq. (8) with constant `C_F` for every
state (Lemma 5.4's assumption); the constant is the explicit `C = C_F + 1`. `p_x Tr(Oψ_x)` is
written `Tr(O φ_xφ_x†)` with `φ_x = (⟨x| ⊗ I)|ψ⟩`, `p_x = ‖φ_x‖₂²`, which avoids dividing by `p_x`
when `p_x = 0`. The data are `N_ℓ` independent bases, each measured with `I_{2^ℓ} ⊗ U_i` on `S_ℓ`
fresh copies of `|ψ⟩` (Eq. (18)); the estimator reads their histograms. The statement is made for
every complex `O` (Corollary 5.10); for Hermitian `O` the estimator is real and the second
conjunct is Lemma 5.9's variance bound. -/
theorem lemma_5_9 (CF : ℝ) (n j : ℕ) (hj : j ≤ n) {ι : Type} [Fintype ι] (E : Primitive j ι)
    (hCl : IsCliffordPrimitive E) (hinv : IsUnit (measChannel E))
    (hvar : ∀ ρ : Op j, WildeQIT.IsDensityOperator ρ → ∀ O : Op j, O.IsHermitian →
      snapVar E ρ O ≤ CF * frobSq O)
    (ψ : Bits n → ℂ) (hψ : IsUnitVec ψ) (x : Bits (n - j)) (N S : ℕ) (hN : 1 ≤ N) (hS : 1 ≤ S)
    (O : Op j) :
    ∑ data : Fin N → ι × (Fin S → Bits (n - j) × Bits j),
        ((levelWeight E ψ data : ℝ) : ℂ) *
          condEst E x O S (fun i => ((data i).1, histOf (data i).2))
      = (O * ketbra (cond ψ x) (cond ψ x)).trace ∧
    ∑ data : Fin N → ι × (Fin S → Bits (n - j) × Bits j),
        levelWeight E ψ data *
          ‖condEst E x O S (fun i => ((data i).1, histOf (data i).2))
            - (O * ketbra (cond ψ x) (cond ψ x)).trace‖ ^ 2
      ≤ (CF + 1) * frobSq O / N *
          (vnormSq (cond ψ x) ^ 2 + vnormSq (cond ψ x) / S) := by sorry

end ShadowBootstrap
