-- Prove2me | Theorems.Thm_QSDMixing_GU_exists_covariant_povm
-- name    : QSDMixing.GU.exists_covariant_povm
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:56:00.111827+00:00
-- url     : https://prove2.me/theorems/2501024d-afa0-40e7-9e7b-21ea1ab9bdc3
-- title:
--   §3, p.18 — on a GU ensemble, the averaged measurement equalizes success, and $k_{\min}=k_{\mathrm{wc}}$
-- statement:
--   Consider a geometrically uniform ensemble on $G/H$, with $n=|G/H|$, and $t\ge1$ copies. There are unitaries $W_k$, $k\in G$, on the $t$-copy space acting as $U_k^{\otimes t}$ on pure tensors, such that for any POVM $(\Pi_x)_{x\in G/H}$ on $t$ copies, the averaged measurement
--
--   $$
--   \bar\Pi_x=\frac1{|G|}\sum_{k\in G}W_k\,\Pi_{k^{-1}x}\,W_k^\dagger
--   $$
--
--   is a POVM, and for every label $x$,
--
--   $$
--   \mathrm{tr}\big(\bar\Pi_x\,(|\psi_x\rangle\langle\psi_x|)^{\otimes t}\big)=\frac1n\sum_y\mathrm{tr}\big(\Pi_y\,(|\psi_y\rangle\langle\psi_y|)^{\otimes t}\big).
--   $$
--
--   Consequently $k_{\min}(\epsilon)=k_{\mathrm{wc}}(\epsilon)$.
--
--   This is what allows the stability of worst-case sample complexity (Proposition 9) to be applied to the average-case quantity $k_{\min}$.
--
--   Differences from the source:
--   - reading: U_k in the formula for Π̄_{gH}, on t copies → W_k, a unitary on ℓ²(Fin t → ι) acting on pure tensors as U_k in every factor, its existence asserted; reason: on t copies the operator must be the tensor power, and pure tensors determine it uniquely; no such operator is assumed
--   - generalization: ε ∈ (0, 1), the range of k_min on p.3 → every real ε; reason: the equality follows for each ε from the first clause alone, and it specializes to the source's range
--   - reading: "a Hilbert space ℋ", with no dimension → every ℓ²(ι), for an arbitrary type ι, with k-fold tensor power ℓ²(Fin k → ι); reason: every complex Hilbert space is unitarily ℓ²(ι), and the finite-dimensional reading would be the weaker one
--   - reading: minimum over an unstated range of k and t → minimum over k, t ≥ 1; reason: the paper's ℕ in (52) starts at 1 (eq. (15) writes s ≥ 1), and with t = 0 allowed Theorem 2 fails at A = ℂ·1; for n ≥ 2 the value does not change
--   - encoding: k_min, k_wc, t_min and t_mix as numbers → values in ℕ∞, with ⊤ when no count qualifies; reason: the minima can be over an empty set, where Lean's ℕ-valued sInf would give the junk value 0
--   - encoding: max over POVMs at least 1 − ε → there exists a POVM reaching at least 1 − ε; reason: equivalent whenever the maximum exists, and it does not assume attainment
--   - encoding: pure states |ψ_{gH}⟩ with uniform prior → MixedState.pure of U_{x.out} ψ, the prior 1/n built into kMin; reason: the vector does not depend on the representative, because U_h ψ = ψ on H
-- source:
--   Zhou, Leditzky, A mixing time method for estimating the sample complexity of quantum state discrimination, arXiv:2609.40182 (held version, sha256 62fb68dd…), §3, unnumbered paragraph, p.18

import Mathlib
import Definitions.Def_GaussTesting_Ell2
import Definitions.Def_QSDMixing_GU_tensorVec
import Definitions.Def_QSDMixing_GU_MixedState
import Definitions.Def_QSDMixing_GU_IsPOVM
import Definitions.Def_QSDMixing_GU_copyEffect
import Definitions.Def_QSDMixing_GU_stabilizer
import Definitions.Def_QSDMixing_GU_cosetFintype
import Definitions.Def_QSDMixing_GU_cosetEnsemble
import Definitions.Def_QSDMixing_GU_kMin
import Definitions.Def_QSDMixing_GU_kWc

set_option autoImplicit false
open GaussTesting (Ell2)

namespace QSDMixing.GU

/-- **§3, unnumbered, p.18.** On a geometrically uniform ensemble the average and the worst case coincide. For any POVM
`{Π_{gH}}` on `t` copies, the averaged measurement `Π̄_{gH} = (1/|G|) Σ_{k∈G} U_k Π_{k⁻¹gH} U_k†` is a POVM with every
conditional success equal to the average success of `Π`, and so `k_min(ε) = k_wc(ε)`.

Zhou, Leditzky, *A mixing time method for estimating the sample complexity of quantum state discrimination*, arXiv:2609.40182 (held version, sha256 62fb68dd…), §3, p.18: "the optimal average success probability coincides with the optimal worst-case success
probability".

**Formalization Note.** On `t` copies the page's `U_k` is the tensor power `U_k^{⊗t}`. It is `W k` here: a unitary on
`ℓ²(Fin t → ι)` acting on pure tensors as `U_k` in every factor, which pure tensors determine uniquely. Its existence is part of the
claim, so nothing is assumed about it. Equal conditional successes give the page's "same average success". The equality of `kMin` and `kWc`
is the conclusion of the paragraph and holds for every real `ε`. -/
theorem exists_covariant_povm {G ι : Type} [Group G] [Fintype G]
    (U : G →* unitary (Ell2 ι →L[ℂ] Ell2 ι)) (ψ : Ell2 ι) (hψ : ‖ψ‖ = 1) :
    (∀ t : ℕ, 1 ≤ t →
      ∃ W : G → Ell2 (Fin t → ι) →L[ℂ] Ell2 (Fin t → ι),
        (∀ k, W k ∈ unitary (Ell2 (Fin t → ι) →L[ℂ] Ell2 (Fin t → ι))) ∧
        (∀ (k : G) (v : Fin t → Ell2 ι),
          W k (tensorVec v) = tensorVec fun j => (U k : Ell2 ι →L[ℂ] Ell2 ι) (v j)) ∧
        ∀ M : G ⧸ stabilizer U ψ → Ell2 (Fin t → ι) →L[ℂ] Ell2 (Fin t → ι), IsPOVM M →
          let Mbar : G ⧸ stabilizer U ψ → Ell2 (Fin t → ι) →L[ℂ] Ell2 (Fin t → ι) := fun x =>
            ((1 / (Fintype.card G : ℝ) : ℝ) : ℂ) • ∑ k : G, W k * M (k⁻¹ • x) * star (W k)
          IsPOVM Mbar ∧
            ∀ x, copyEffect (cosetEnsemble U ψ hψ x) t (Mbar x) =
              (1 / (Fintype.card (G ⧸ stabilizer U ψ) : ℝ)) *
                ∑ y, copyEffect (cosetEnsemble U ψ hψ y) t (M y)) ∧
    ∀ ε : ℝ, kMin (cosetEnsemble U ψ hψ) ε = kWc (cosetEnsemble U ψ hψ) ε := by sorry

end QSDMixing.GU
