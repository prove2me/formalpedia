-- Prove2me | Theorems.Thm_SingleExpBisect_Main_lemma_3_7
-- name    : SingleExpBisect.Main.lemma_3_7
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T17:40:38.185934+00:00
-- url     : https://prove2.me/theorems/37dec473-5192-4039-b556-5884dcba3523
-- title:
--   Lemma 3.7 — Φ_t(S) is well defined: the minimizers of µ_t(S) have a largest member
-- statement:
--   For every graph $G$, $W\subseteq V(G)$ (playing $V(G_t)$) and $S\subseteq W$, the family $\{A\subseteq V(G): A\cap W=S,\ |\delta_G(A)|=\mu_t(S)\}$ has an inclusion-wise largest member, and it is $\Phi_t(S)$.
--
--   Differences from the source:
--   - generalization: W = V(G_t) for a node of the Section 3 decomposition → any W ⊆ V(G); reason: the proof (p. 24) uses only submodularity of the cut function
--   - encoding: "Φ_t(S) is well-defined" → IsGreatest of the family at Phi G W S (defined as the union of the family); reason: well-definedness is the existence of a largest member; when it exists it is the union
-- source:
--   Kumabe, Single-Exponential FPT Algorithms for Minimum Bisection and Matching Cut via a New Unbreakable Decomposition, arXiv:2611.05982 (October 2026 version; PDF SHA256 6530ce94…6b76541), §3.4, p. 24, Lemma 3.7

import Mathlib
import Definitions.Def_SingleExpBisect_Main_NodeData

open scoped Classical

namespace SingleExpBisect.Main

open MinBisectFPT

/-- Kumabe, *Single-Exponential FPT Algorithms for Minimum Bisection and Matching Cut via a New
Unbreakable Decomposition*, arXiv:2611.05982 (October 2026), §3.4, p. 24, Lemma 3.7: for every
`S ⊆ W` (`W = V(G_t)`), the family `{A ⊆ V(G) : A ∩ W = S, |δ_G(A)| = µ_t(S)}` has an
inclusion-wise largest member, namely `Φ_t(S)`. -/
theorem lemma_3_7 {n : ℕ} (G : SimpleGraph (Fin n)) (W S : Finset (Fin n)) (hS : S ⊆ W) :
    IsGreatest {A : Finset (Fin n) | A ∩ W = S ∧ cutSize G A = mu G W S} (Phi G W S) := by sorry

end SingleExpBisect.Main
