-- Prove2me | Theorems.Thm_SetCoverThreshold_SetCover_scInst_cover_gap
-- name    : SetCoverThreshold.SetCover.scInst_cover_gap
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-10-30T19:43:59.856842+00:00
-- url     : https://prove2.me/theorems/5f43f1dd-6d54-423a-b3fd-0b39fe884363
-- title:
--   Coverability and cover-size gap of the §4 Set Cover instance scInst (Feige 1998, Lemma 4.1)
-- statement:
--   Coverability and cover-size gap of the §4 Set Cover reduction instance $\mathrm{scInst}$ (Feige 1998, Lemma 4.1, p. 645): every $\mathrm{scInst}(\varphi, \mathrm{code}, P)$ is coverable. If $\varphi$ is satisfiable, then $\mathrm{scInst}(\varphi, \mathrm{code}, P)$ has a cover of size at most $k \cdot |\varphi.\mathrm{numQuestions}(\ell)|$. If at most a $(1 - \varepsilon)$-fraction of the clauses of $\varphi$ are simultaneously satisfiable, then under appropriate parallel repetition and partition system parameters, every cover has size at least $(1 - 2f) \cdot k \cdot |\varphi.\mathrm{numQuestions}(\ell)| \cdot \ln m$.
-- source:
--   Feige 1998, A Threshold of ln n for Approximating Set Cover, J. ACM 45(4): 634–652, Lemma 4.1, p. 645

import Definitions.Def_CookPvsNP_defs
import Definitions.Def_SetCoverThreshold_SetCover_Formula
import Definitions.Def_SetCoverThreshold_SetCover_ProofSystem
import Definitions.Def_SetCoverThreshold_SetCover_PartitionSystem
import Definitions.Def_SetCoverThreshold_SetCover_Instance
import Definitions.Def_SetCoverThreshold_SetCover_Reduction
import Definitions.Def_SetCoverThreshold_SetCover_Theorem44

namespace SetCoverThreshold.SetCover

/-- **Coverability and cover-size gap of the §4 Set Cover instance `scInst`** (Feige 1998, Lemma 4.1,
p. 645): every `scInst φ code P` is coverable; if `φ` is satisfiable then `scInst φ code P` has a
cover of cardinality at most `k · φ.numQuestions ℓ`; and if at most a `(1 - ε)`-fraction of the
clauses of `φ` are simultaneously satisfiable, every cover of `scInst φ code P` has cardinality at
least `(1 - 2f) · k · φ.numQuestions ℓ · ln m`. -/
theorem scInst_cover_gap (hRaz : RazRepetition) (ε : ℝ) (hε : 0 < ε) :
    ∃ c : ℝ, 0 < c ∧
      ∀ (φ : Formula5) (ℓ k m d : ℕ) (code : Fin k → Fin ℓ → Bool), IsCode ℓ k code →
        ∀ P : φ.RandomString ℓ → PartitionSystem m (2 ^ ℓ) k d,
          (scInst φ code P).Coverable ∧
          (φ.toCNF.Satisfiable →
              ∃ C : Finset (Fin (scInst φ code P).sets.length),
                (scInst φ code P).IsCover C ∧ C.card ≤ k * φ.numQuestions ℓ) ∧
            ∀ f : ℝ, 0 < f → (1 - f) * k * Real.log m ≤ d →
              (k : ℝ) ^ 2 * (2 : ℝ) ^ (-(c * ℓ)) < 2 * (2 * f) / (k * Real.log m) ^ 2 →
                AtMostFracSat (1 - ε) φ.toCNF →
                  ∀ C : Finset (Fin (scInst φ code P).sets.length),
                    (scInst φ code P).IsCover C →
                      (1 - 2 * f) * k * φ.numQuestions ℓ * Real.log m ≤ C.card := by sorry

end SetCoverThreshold.SetCover
