-- Prove2me | Theorems.Thm_UnderstandingML_sign_nets_all_boolean
-- name    : UnderstandingML.sign_nets_all_boolean
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T05:00:03.11799+00:00
-- url     : https://prove2.me/theorems/cd60a0e7-a9e3-4643-aadd-90ca7dbbe98f
-- title:
--   Claim 20.1: for every n there is a depth-2 graph (widths n+1, 2^n+1, 1, all edges) whose sign class contains every function {±1}^n → {±1}
-- statement:
--   **Claim 20.1.** For every $n$, there exists a graph $(V, E)$ of depth $2$, such that $H_{V,E,\operatorname{sign}}$ contains all functions from $\{\pm1\}^n$ to $\{\pm1\}$.
--
--   Formally: the graph of the proof, $|V_0| = n+1$, $|V_1| = 2^n + 1$, $|V_2| = 1$ with all edges between adjacent layers, and $\pm1$ encoded by `Bool`.
-- source:
--   Shalev-Shwartz and Ben-David, Understanding Machine Learning: From Theory to Algorithms, Cambridge University Press 2014, doi:10.1017/CBO9781107298019, §20.3 p. 271, Claim 20.1 with its proof

import Definitions.Def_UnderstandingML_NeuralNetworks

open MeasureTheory

namespace UnderstandingML

/-- **Claim 20.1** (p. 271). For every `n`, there exists a graph `(V, E)` of depth `2`, such
that `H_{V,E,sign}` contains all functions from `{±1}^n` to `{±1}`.
The graph has `|V₀| = n + 1`, `|V₁| = 2^n + 1`, `|V₂| = 1` and all edges between adjacent
layers; `±1` is encoded by `Bool` (`true ↦ 1`). -/
theorem sign_nets_all_boolean (n : ℕ) :
    ∃ G : LayeredGraph, G.depth = 2 ∧ G.width 0 = n + 1 ∧ G.width 1 = 2 ^ n + 1 ∧
      G.width 2 = 1 ∧ G.numEdges = (n + 1) * (2 ^ n + 1) + (2 ^ n + 1) ∧
      ∀ f : (Fin n → Bool) → Bool, ∃ h ∈ signNetClass n G,
        ∀ x : Fin n → Bool, h (fun i ↦ if x i then (1 : ℝ) else -1) = f x := by sorry

end UnderstandingML
