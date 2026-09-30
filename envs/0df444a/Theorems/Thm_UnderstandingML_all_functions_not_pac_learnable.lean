-- Prove2me | Theorems.Thm_UnderstandingML_all_functions_not_pac_learnable
-- name    : UnderstandingML.all_functions_not_pac_learnable
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T03:36:38.176767+00:00
-- url     : https://prove2.me/theorems/669a1b9a-234d-4037-a193-484b42ae2bae
-- title:
--   Corollary 5.2: for an infinite domain X the class of all functions X → {0,1} is not PAC learnable
-- statement:
--   **Corollary 5.2.** Let $X$ be an infinite domain set and let $H$ be the set of all functions from $X$ to $\{0,1\}$. Then, $H$ is not PAC learnable.
--
--   Formally: for an infinite domain $X$ with measurable singletons, the class of all functions $X \to \{0,1\}$ is not PAC learnable in the sense of Definition 3.1 (`PACLearnable`).
-- source:
--   Shalev-Shwartz and Ben-David, Understanding Machine Learning: From Theory to Algorithms, Cambridge University Press 2014, doi:10.1017/CBO9781107298019, §5.1.1 pp. 63-64, Corollary 5.2 with its proof

import Definitions.Def_UnderstandingML_Framework
import Mathlib.SetTheory.Cardinal.Finite

open MeasureTheory

namespace UnderstandingML

/-- **Corollary 5.2** (p. 63). Let `X` be an infinite domain set and let `H` be the set of all
functions from `X` to `{0, 1}`. Then `H` is not PAC learnable. The domain has measurable
singletons (Remark 3.1). -/
theorem all_functions_not_pac_learnable {X : Type*} [MeasurableSpace X]
    [MeasurableSingletonClass X] [Infinite X] :
    ¬ PACLearnable (Set.univ : Set (X → Bool)) := by sorry

end UnderstandingML
