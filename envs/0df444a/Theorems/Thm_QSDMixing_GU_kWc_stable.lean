-- Prove2me | Theorems.Thm_QSDMixing_GU_kWc_stable
-- name    : QSDMixing.GU.kWc_stable
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:55:47.375494+00:00
-- url     : https://prove2.me/theorems/8e84e172-098b-4091-94dd-db493a4b9a3f
-- title:
--   Proposition 9 — stability of worst-case sample complexity, $k_{\mathrm{wc}}(\epsilon)=\Theta_{\epsilon,\delta}k_{\mathrm{wc}}(\delta)$
-- statement:
--   For $0<\epsilon\le\delta<\frac12$ there is an integer $m=m(\epsilon,\delta)\ge1$ such that, for every finite ensemble of states on every Hilbert space,
--
--   $$
--   k_{\mathrm{wc}}(\delta)\le k_{\mathrm{wc}}(\epsilon)\le m\,k_{\mathrm{wc}}(\delta).
--   $$
--
--   Worst-case discrimination can therefore be amplified at a constant cost. The paper notes that average-case discrimination has no such property in general.
--
--   **Formalization Note** Both sides may be infinite.
--
--   Differences from the source:
--   - reading: Θ_{ε,δ} → one integer m chosen after ε, δ and before the ensemble, with two inequalities; reason: the proof on the page takes m = m(ε, δ) and gets k_wc(δ) ≤ k_wc(ε) ≤ m(ε, δ) k_wc(δ)
--   - reading: "a Hilbert space ℋ", with no dimension → every ℓ²(ι), for an arbitrary type ι, with k-fold tensor power ℓ²(Fin k → ι); reason: every complex Hilbert space is unitarily ℓ²(ι), and the finite-dimensional reading would be the weaker one
--   - encoding: density operators ρ_i on ℋ → countable mixtures Σ_a w_a |v_a⟩⟨v_a| of unit vectors, with tr(M ρ^{⊗k}) expanded over Fin k → ℕ; reason: the spectral theorem gives every density operator this form; it avoids a trace-class layer and loses no instance
--   - reading: minimum over an unstated range of k and t → minimum over k, t ≥ 1; reason: the paper's ℕ in (52) starts at 1 (eq. (15) writes s ≥ 1), and with t = 0 allowed Theorem 2 fails at A = ℂ·1; for n ≥ 2 the value does not change
--   - encoding: k_min, k_wc, t_min and t_mix as numbers → values in ℕ∞, with ⊤ when no count qualifies; reason: the minima can be over an empty set, where Lean's ℕ-valued sInf would give the junk value 0
--   - encoding: max over POVMs at least 1 − ε → there exists a POVM reaching at least 1 − ε; reason: equivalent whenever the maximum exists, and it does not assume attainment
-- source:
--   Zhou, Leditzky, A mixing time method for estimating the sample complexity of quantum state discrimination, arXiv:2609.40182 (held version, sha256 62fb68dd…), §2.1, Proposition 9, eq. (36), p.12

import Mathlib
import Definitions.Def_GaussTesting_Ell2
import Definitions.Def_QSDMixing_GU_MixedState
import Definitions.Def_QSDMixing_GU_kWc

set_option autoImplicit false
open GaussTesting (Ell2)

namespace QSDMixing.GU

/-- **Proposition 9, p.12.** Worst-case sample complexity is stable under constant changes of the error
tolerance: for `ε ≤ δ` in `(0, 1/2)`, `k_wc(ε) = Θ_{ε,δ} k_wc(δ)`, that is,
`k_wc(δ) ≤ k_wc(ε) ≤ m(ε, δ) k_wc(δ)`.

Zhou, Leditzky, *A mixing time method for estimating the sample complexity of quantum state discrimination*, arXiv:2609.40182 (held version, sha256 62fb68dd…), §2.1, Proposition 9, eq. (36), p.12.

**Formalization Note.** `m` is chosen after `ε, δ` and before the ensemble, as the paper's `m(ε, δ)` is: one factor for
every finite ensemble of states on every Hilbert space. The inequalities are in `ℕ∞`, and both sides may be `⊤`. -/
theorem kWc_stable (ε δ : ℝ) (hε : 0 < ε) (hεδ : ε ≤ δ) (hδ : δ < 1 / 2) :
    ∃ m : ℕ, 1 ≤ m ∧
      ∀ (ι I : Type) [Fintype I] (e : I → MixedState ι),
        kWc e δ ≤ kWc e ε ∧ kWc e ε ≤ (m : ℕ∞) * kWc e δ := by sorry

end QSDMixing.GU
