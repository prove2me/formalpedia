-- Prove2me | Theorems.Thm_ThresholdTheorem_isLocalStochastic_relabel
-- name    : ThresholdTheorem.isLocalStochastic_relabel
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-25T20:32:44.104955+00:00
-- url     : https://prove2.me/theorems/4d7825b7-4ec5-4120-8967-9dc50055fc00
-- title:
--   Local stochastic noise is invariant under relabelling qubits
-- statement:
--   Let $\sigma:Q\simeq Q'$ be a bijection between finite sets of qubits, let $C$ be a layered circuit on $Q$ and let $C^\sigma$ be the same circuit with its qubits renamed by $\sigma$ (same layers, same location order). If $P$ is an output distribution of $C^\sigma$ under local stochastic noise of rate $e$, then the relabelled distribution $x\mapsto P(x\circ\sigma^{-1})$, written as the push-forward of $P$ along $x'\mapsto x'\circ\sigma$, is an output distribution of $C$ under local stochastic noise of rate $e$.
--
--   The same fault sets, weights and fault channels work, because locations are indexed by (layer, position) and relabelling commutes with the lifted Kraus operators. This is the bookkeeping step that identifies nested blocks $(Q\times\mathrm{Fin}\,b_k)\times\mathrm{Fin}\,b$ with $Q\times\mathrm{Fin}(b_k b)$ in concatenated codes.
-- source:
--   Structural lemma for the concatenated-code construction in D. Gottesman, arXiv:0904.2557, Sec. 5 (blocks of blocks at level k); stated for Definitions.Def_threshold_theorem_local_stochastic.

import Mathlib
import Definitions.Def_threshold_theorem_local_stochastic

open ThresholdTheorem

namespace ThresholdTheorem
theorem isLocalStochastic_relabel {Q Q' : Type*} [Fintype Q] [DecidableEq Q] [Fintype Q']
    [DecidableEq Q'] (σ : Q ≃ Q') (C : Circuit Q) (e : ℝ) (P : (Q' → Fin 2) → ℝ)
    (hP : IsLocalStochasticDist (C.relabel σ) e P) :
    IsLocalStochasticDist C e (pushDist (fun x => x ∘ σ) P) := by sorry
end ThresholdTheorem
