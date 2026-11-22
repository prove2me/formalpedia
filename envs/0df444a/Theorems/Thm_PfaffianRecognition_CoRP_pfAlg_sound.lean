-- Prove2me | Theorems.Thm_PfaffianRecognition_CoRP_pfAlg_sound
-- name    : PfaffianRecognition.CoRP.pfAlg_sound
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-22T21:25:16.773053+00:00
-- url     : https://prove2.me/theorems/5108d0c9-5e5b-4238-a23f-d0c13cea2199
-- title:
--   The randomized Pfaffian recognition algorithm rejects non-instances with probability at least 1/2
-- statement:
--   If $w$ is not the encoding of a Pfaffian graph, then on a uniformly random string $\rho$ of length $(|w|+2)^8$ the randomized recognition algorithm rejects with probability at least $\tfrac12$:
--   $$w\notin L_{\mathrm{Pf}}\Longrightarrow \Pr_{\rho\in\{0,1\}^{(|w|+2)^8}}\bigl[\mathcal A(\rho,w)=0\bigr]\ge\tfrac12 .$$
--
--   Malformed strings are always rejected. For a non-Pfaffian graph $G$ with $N$ vertices and edge set $E$, no $(d,s)$ is consistent with all perfect matchings, so in every round the wrong-sign polynomial $Q_{d,s}(x)=\sum_{M\text{ inconsistent}}\prod_{e\in M}x_e^2$ is nonzero of degree at most $N$; by the Schwartz–Zippel lemma a fresh random point of $\mathbb F_{2^{2m}}^E$ is a root with probability at most $N/2^{2m}$. Whenever it is not a root, the greedy search returns an inconsistent perfect matching, and each added equation is linearly independent of the previous ones, so after at most $|E|+2$ such rounds the system becomes inconsistent and the algorithm rejects. A union bound over the $|E|+3$ rounds gives the claim. This is the soundness half of Theorem 1.1, following Theorem 3.2 and Lemmas 2.1, 2.3, 3.1.
--
--   **Formalization Note** Probabilities are counts over all tapes $\omega\in\{0,1\}^{(|w|+2)^8}$ (`fairProb`), read as the bit list `tapeList ω`.
-- source:
--   Priyanshu Pant, Ranveer Singh, Pfaffian Recognition is in coRP, STOC 2027 submission #858 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/858.pdf, Theorem 1.1 (p. 3) with proof on p. 8, Theorem 3.2 (p. 7), Lemmas 2.1, 2.3 (pp. 5-6), Lemma 3.1 (Schwartz-Zippel, p. 7)

import Definitions.Def_PfaffianRecognition_CoRP_Algorithm
import Definitions.Def_PfaffianRecognition_Recognition_computation_model

namespace PfaffianRecognition.CoRP

theorem pfAlg_sound (w : List Bool) (h : ¬ PfaffianRecognition.Recognition.pfaffianLanguage w) :
    (1 / 2 : ℝ) ≤ HypergraphUnreliability.FPRAS.fairProb ((w.length + 2) ^ 8)
      (fun ω => pfAlg (HypergraphUnreliability.FPRAS.tapeList ω, w) = false) := by sorry

end PfaffianRecognition.CoRP
