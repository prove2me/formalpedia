-- Prove2me | Theorems.Thm_RobustKellyTV_theorem_2_5
-- name    : RobustKellyTV.theorem_2_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:35:11.790122+00:00
-- url     : https://prove2.me/theorems/136605d1-dbec-494f-8ad5-d46b91a1ca52
-- title:
--   Theorem 2.5 — $M^{\mathrm{CK}}$ is a test supermartingale under $\mathcal P_0$, for every positive pseudocount vector
-- statement:
--   Assume the standing assumptions and fix positive pseudocounts $\alpha_1,\dots,\alpha_d>0$. The adaptive clipped-Kelly process $(M^{\mathrm{CK}}_n)_n$ is a nonnegative test supermartingale under $\mathcal P_0$: $M^{\mathrm{CK}}_0=1$, $M^{\mathrm{CK}}_n\ge0$, and under every i.i.d. law $R^\infty$ with $R\in\mathcal P_0$ it is a supermartingale for $\mathcal F_n=\sigma(X_1,\dots,X_n)$.
--
--   As the paper notes, this validity holds for every choice of positive pseudocounts and requires no accuracy of the predictor.
--
--   Differences from the source:
--   - encoding: test supermartingale under P0 → M_0 = 1, M ≥ 0, and a supermartingale for the prefix filtration under every i.i.d. law R^∞ with R ∈ P0; reason: the paper's reading in the proofs of Theorems 2.5 and 3.2 (pp.23, 29)
--   - encoding: i.i.d. observations X_1, X_2, … from S → the infinite product law of S on ℕ → Fin d, with X_t the coordinate t − 1; reason: every process is a function of the observed prefix, so no instance changes
-- source:
--   A. Saha, A. Ramdas, Beyond least-favorable distribution pairs: asymptotically instance-optimal robust hypothesis testing, arXiv:2611.02130v1, §2.2, Theorem 2.5 and the following sentence, p.9 (proof p.23)

import Mathlib
import Definitions.Def_RobustKellyTV_seqLaw
import Definitions.Def_RobustKellyTV_Mck

namespace RobustKellyTV

/-- **Theorem 2.5**. A. Saha, A. Ramdas, *Beyond least-favorable distribution pairs: asymptotically instance-optimal
robust hypothesis testing*, arXiv:2611.02130v1, Theorem 2.5, p.9.

The process `(M^CK_n)_n` is a nonnegative test supermartingale under `P` (the null class `P0`).
"This validity statement holds for every choice of positive pseudocounts" (p.9).

**Formalization Note.** Standing assumptions (p.6): `d ≥ 2`, `Pᵢ > 0`, `0 < ϵ0 < 1 − minᵢ Pᵢ`, bundled in `σ : Setting d`. Stated for every vector of positive pseudocounts. A test
supermartingale under `P0` is: `M₀ = 1`, `M ≥ 0`, and a supermartingale for the prefix filtration
under every i.i.d. law `R^∞` with `R ∈ P0` (the proof, p.23). -/
theorem theorem_2_5 {d : ℕ} (σ : Setting d) (pc : Fin d → ℝ) (hpc : ∀ i, 0 < pc i) :
    IsTestSupermartingale σ (Mck σ pc) := by sorry

end RobustKellyTV
