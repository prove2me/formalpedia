-- Prove2me | Theorems.Thm_UnderstandingML_vcDim_sign_net
-- name    : UnderstandingML.vcDim_sign_net
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T05:05:31.835205+00:00
-- url     : https://prove2.me/theorems/4e82a9af-2d58-446a-97c0-1664d90382d5
-- title:
--   Theorem 20.6: the VC dimension of H_{V,E,sign} is O(|E| log |E|); explicitly VCdim ≤ 2|E| log₂(16|E|)
-- statement:
--   **Theorem 20.6.** The VC dimension of $H_{V,E,\operatorname{sign}}$ is $O(|E|\log(|E|))$.
--
--   Formally, with explicit constants: for a layered graph of depth $\ge 1$ with a single output neuron, every $m \le \operatorname{VCdim}(H_{V,E,\operatorname{sign}})$ satisfies $m \le 2|E|\log_2(16|E|)$ (from $2^m \le (em)^{|E|}$ for a shattered set of size $m$); in particular the VC dimension is finite.
-- source:
--   Shalev-Shwartz and Ben-David, Understanding Machine Learning: From Theory to Algorithms, Cambridge University Press 2014, doi:10.1017/CBO9781107298019, §20.4 pp. 274-275, Theorem 20.6 with its proof

import Definitions.Def_UnderstandingML_NeuralNetworks

open MeasureTheory

namespace UnderstandingML

/-- **Theorem 20.6** (p. 274). The VC dimension of `H_{V,E,sign}` is `O(|E| log(|E|))`.
Explicitly, with the constants the proof gives (`2^m ≤ (em)^{|E|}` for a shattered set of size
`m`): `VCdim(H_{V,E,sign}) ≤ 2|E| log₂(16|E|)`, for a network of depth at least `1` with a
single output neuron. -/
theorem vcDim_sign_net (n : ℕ) (G : LayeredGraph) (hd : 1 ≤ G.depth) (m : ℕ)
    (hm : (m : ℕ∞) ≤ vcDim (signNetClass n G)) :
    (m : ℝ) ≤ 2 * G.numEdges * Real.logb 2 (16 * G.numEdges) := by sorry

end UnderstandingML
