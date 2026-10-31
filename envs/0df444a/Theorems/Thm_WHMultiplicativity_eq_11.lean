-- Prove2me | Theorems.Thm_WHMultiplicativity_eq_11
-- name    : WHMultiplicativity.eq_11
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T15:23:39.414226+00:00
-- url     : https://prove2.me/theorems/f4ad4a0d-d6c4-420f-ac62-59418327e57b
-- title:
--   Eq. (11): $\|S\otimes S(|\Phi_m\rangle\langle\Phi_m|)\|_p = \frac13\big(1+2^{3-2p}\big)^{1/p}$ for $d = 3$
-- statement:
--   Let $S$ be the Werner–Holevo channel on $3\times3$ matrices, $S(\rho) = \tfrac12(\operatorname{tr}(\rho)\mathbb 1 - \rho^T)$, and let $\Phi_m = \tfrac{1}{\sqrt3}\sum_{\alpha}|\alpha\alpha\rangle$ be the maximally entangled vector in $\mathbb C^3\otimes\mathbb C^3$. For every real $p > 1$,
--
--   $$
--   \big\|S\otimes S(|\Phi_m\rangle\langle\Phi_m|)\big\|_p = \frac13\big(1 + 2^{3-2p}\big)^{1/p},
--   $$
--
--   and for $p = \infty$ (operator norm) $\|S\otimes S(|\Phi_m\rangle\langle\Phi_m|)\|_\infty = \tfrac13$.
--
--   The output has eigenvalue $\tfrac1{12}$ with multiplicity $8$ and the simple eigenvalue $\tfrac13$.
--
--   Differences from the source:
--   - generalization: (11) for 1 < p < ∞ → also the value 1/3 at p = ∞; reason: the limit p → ∞ of (11), used by the page for Δ(∞, Φm); the finite-p clause is the page's statement
--   - encoding: S ⊗ S on ℂ^d ⊗ ℂ^d → QAlgorithms.piSuperop (fun _ : Fin 2 => S) on matrices indexed by Fin 2 → Fin d; reason: the tensor product of superoperators through matrix units, on every input (entangled ones included); y : Fin 2 → Fin d is the basis vector |y 0⟩ ⊗ |y 1⟩
--   - encoding: ‖X‖_p = (tr|X|^p)^{1/p} for real p, and ‖·‖_∞ the operator norm → schattenNorm p X with p : ℝ≥0∞, a real p entering as ENNReal.ofReal p and ∞ as ⊤; reason: tr|X|^p = tr (XᴴX)^{p/2}; ⊤ gives the ℓ² operator norm; same values
-- source:
--   Werner and Holevo, Counterexample to an additivity conjecture for output purity of quantum channels, arXiv:quant-ph/0203003v1, eq. (11), p.2 (p = ∞ value as used after eq. (13))

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_WHAdditivity_Renyi_Model
import Definitions.Def_WHMultiplicativity_schattenNorm
import Definitions.Def_WHMultiplicativity_maxEnt

open scoped ENNReal
open WHAdditivity.Renyi

namespace WHMultiplicativity

/-- Werner and Holevo, arXiv:quant-ph/0203003v1, eq. (11), p.2: for `d = 3` and the maximally
entangled vector `Φ_m` (all `c_α = 1/√3`), `‖S ⊗ S(|Φ_m⟩⟨Φ_m|)‖_p = (1/3)(1 + 2^{3−2p})^{1/p}`;
and (the `p = ∞` value used after eq. (13)) `‖S ⊗ S(|Φ_m⟩⟨Φ_m|)‖_∞ = 1/3`.

**Formalization Note.** `S = wernerHolevo 3`, `S ⊗ S = QAlgorithms.piSuperop (fun _ : Fin 2 => S)`
on `ℂ³ ⊗ ℂ³` (index `Fin 2 → Fin 3`), `Φ_m = maxEnt 3`, `‖·‖_p = schattenNorm`. A real `p` with
`1 < p` (the paper's range) enters as `ENNReal.ofReal p`; `p = ∞` is `⊤` (operator norm). -/
theorem eq_11 :
    (∀ p : ℝ, 1 < p →
        schattenNorm (ENNReal.ofReal p)
            (QAlgorithms.piSuperop (fun _ : Fin 2 => wernerHolevo 3) (pureState (maxEnt 3))) =
          (1 / 3) * (1 + (2 : ℝ) ^ (3 - 2 * p)) ^ (1 / p)) ∧
      schattenNorm ⊤
          (QAlgorithms.piSuperop (fun _ : Fin 2 => wernerHolevo 3) (pureState (maxEnt 3))) =
        1 / 3 := by sorry

end WHMultiplicativity
