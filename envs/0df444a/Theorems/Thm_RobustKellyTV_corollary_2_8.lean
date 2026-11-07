-- Prove2me | Theorems.Thm_RobustKellyTV_corollary_2_8
-- name    : RobustKellyTV.corollary_2_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:35:17.281177+00:00
-- url     : https://prove2.me/theorems/54cacb6f-c6b9-4f8e-98a2-eaa9bcc25252
-- title:
--   Corollary 2.8 — $\tfrac1n\log M^{\mathrm{CK}}_n\to\Gamma(S)$ almost surely
-- statement:
--   Assume the standing assumptions, the Laplace pseudocounts, and that the observations are i.i.d. from a fixed full-support $S\in\Delta_d\setminus\mathcal P_0$. Then
--
--   $$\frac1n\log M^{\mathrm{CK}}_n\longrightarrow\Gamma(S)\quad\text{almost surely under }S .$$
--
--   In particular the wealth diverges and the test rejects at every fixed level.
--
--   Differences from the source:
--   - encoding: i.i.d. observations X_1, X_2, … from S → the infinite product law of S on ℕ → Fin d, with X_t the coordinate t − 1; reason: every process is a function of the observed prefix, so no instance changes
-- source:
--   A. Saha, A. Ramdas, Beyond least-favorable distribution pairs: asymptotically instance-optimal robust hypothesis testing, arXiv:2611.02130v1, §2.2, Corollary 2.8, eq. (20), p.10

import Mathlib
import Definitions.Def_RobustKellyTV_kl
import Definitions.Def_RobustKellyTV_seqLaw
import Definitions.Def_RobustKellyTV_Mck

open MeasureTheory Filter Topology
open scoped ENNReal

namespace RobustKellyTV

/-- **Corollary 2.8** (Almost-sure pointwise instance optimality). A. Saha, A. Ramdas, *Beyond least-favorable distribution pairs: asymptotically instance-optimal
robust hypothesis testing*, arXiv:2611.02130v1, Corollary 2.8, eq. (20),
p.10.

Under the assumptions of Corollary 2.7 (Laplace pseudocounts (16); i.i.d. observations from a fixed
full-support `S ∈ ∆_d \ P0`), `(1/n) log M^CK_n → Γ(S)` almost surely under `S`.

**Formalization Note.** Standing assumptions (p.6): `d ≥ 2`, `Pᵢ > 0`, `0 < ϵ0 < 1 − minᵢ Pᵢ`, bundled in `σ : Setting d`. -/
theorem corollary_2_8 {d : ℕ} (σ : Setting d) (S : stdSimplex ℝ (Fin d))
    (hSP : (S : Fin d → ℝ) ∉ nullBall σ) (hSpos : ∀ i, 0 < (S : Fin d → ℝ) i) :
    ∀ᵐ ω ∂(seqLaw S),
      Tendsto (fun n : ℕ => (1 / (n : ℝ)) * Real.log (Mck σ (laplace d) n ω)) atTop
        (𝓝 (Gamma σ S)) := by sorry

end RobustKellyTV
