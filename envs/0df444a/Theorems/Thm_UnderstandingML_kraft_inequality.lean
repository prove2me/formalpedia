-- Prove2me | Theorems.Thm_UnderstandingML_kraft_inequality
-- name    : UnderstandingML.kraft_inequality
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T03:48:39.705882+00:00
-- url     : https://prove2.me/theorems/02f17f6e-3c57-4b71-9621-b3d4c46aba84
-- title:
--   Lemma 7.6 (Kraft inequality): a prefix-free set S of binary strings has ∑_{σ∈S} 2^{−|σ|} ≤ 1
-- statement:
--   **Lemma 7.6 (Kraft Inequality).** If $S \subseteq \{0,1\}^*$ is a prefix-free set of strings, then $\sum_{\sigma \in S} \frac{1}{2^{|\sigma|}} \le 1$.
--
--   Formally: for every finite $F \subseteq S$, $\sum_{\sigma \in F} (1/2)^{|\sigma|} \le 1$ (equivalent to the series bound, the terms being nonnegative).
-- source:
--   Shalev-Shwartz and Ben-David, Understanding Machine Learning: From Theory to Algorithms, Cambridge University Press 2014, doi:10.1017/CBO9781107298019, §7.3 p. 90, Lemma 7.6 with its proof

import Definitions.Def_UnderstandingML_Nonuniform

open MeasureTheory

namespace UnderstandingML

/-- **Lemma 7.6 (Kraft Inequality)** (p. 90). If `S ⊆ {0,1}*` is a prefix-free set of strings,
then `∑_{σ ∈ S} 1/2^{|σ|} ≤ 1` (stated on every finite subfamily, which is the same for a
series of nonnegative terms). -/
theorem kraft_inequality (S : Set (List Bool))
    (hpf : ∀ σ ∈ S, ∀ τ ∈ S, σ ≠ τ → ¬ (σ <+: τ)) :
    ∀ F : Finset (List Bool), ↑F ⊆ S → ∑ σ ∈ F, (1 / 2 : ℝ) ^ σ.length ≤ 1 := by sorry

end UnderstandingML
