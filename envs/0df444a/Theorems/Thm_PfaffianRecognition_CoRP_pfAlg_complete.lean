-- Prove2me | Theorems.Thm_PfaffianRecognition_CoRP_pfAlg_complete
-- name    : PfaffianRecognition.CoRP.pfAlg_complete
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-22T21:24:59.432217+00:00
-- url     : https://prove2.me/theorems/0fbac4d2-8e16-4069-a749-f97ba8137ca5
-- title:
--   Perfect completeness of the randomized Pfaffian recognition algorithm
-- statement:
--   If $w$ is the encoding of a Pfaffian graph $G$, then the randomized recognition algorithm accepts $w$ for every random string $\rho$:
--   $$G\text{ Pfaffian}\Longrightarrow \mathcal A(\rho,w)=1\quad\text{for all }\rho .$$
--
--   Here $\mathcal A$ is the algorithm of the definition `PfaffianRecognition_CoRP_Algorithm`, and Pfaffianity is the mathematical notion: some orientation gives all perfect matchings the same permutation sign. The algorithm rejects only when its collected $\mathbb F_2$ equations become inconsistent; every collected equation $\sum_{e\in M}d_e+s=\operatorname{cr}(M)$ comes from an explicitly verified perfect matching $M$, and a Pfaffian orientation satisfies all of them (Lemma 2.1). This is the perfect-completeness half of Theorem 1.1, valid for every random string, including strings shorter than the algorithm would use.
--
--   **Formalization Note** The input language is `pfaffianLanguage` of the mission's computation model (valid encodings of mathematically Pfaffian graphs).
-- source:
--   Priyanshu Pant, Ranveer Singh, Pfaffian Recognition is in coRP, STOC 2027 submission #858 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/858.pdf, Theorem 1.1 (p. 3) with proof on p. 8, Lemma 2.1 (p. 5)

import Definitions.Def_PfaffianRecognition_CoRP_Algorithm
import Definitions.Def_PfaffianRecognition_Recognition_computation_model

namespace PfaffianRecognition.CoRP

theorem pfAlg_complete (ρ w : List Bool) (h : PfaffianRecognition.Recognition.pfaffianLanguage w) :
    pfAlg (ρ, w) = true := by sorry

end PfaffianRecognition.CoRP
