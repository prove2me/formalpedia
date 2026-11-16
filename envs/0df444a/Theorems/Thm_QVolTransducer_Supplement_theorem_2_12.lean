-- Prove2me | Theorems.Thm_QVolTransducer_Supplement_theorem_2_12
-- name    : QVolTransducer.Supplement.theorem_2_12
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T02:35:02.412755+00:00
-- url     : https://prove2.me/theorems/8716b0bd-0d30-4bcc-8dca-ad9225f413c2
-- title:
--   Theorem 2.12 — catalysts of a unidirectional canonical transducer are a feasible adversary solution
-- statement:
--   Let $\mathcal D$ be a set, $U\in\mathcal U(\mathcal V\oplus(\mathcal H\otimes\mathcal W))$ and $\{O_x\}_{x\in\mathcal D}\subseteq\mathcal U(\mathcal H)$. Suppose that the unidirectional canonical transducer $T(O_x):=U(I_{\mathcal V}\oplus(O_x\otimes I_{\mathcal W}))$ implements
--
--   $$|\sigma_x\rangle\oplus|w_x\rangle\ \longmapsto\ |\tau_x\rangle\oplus|w_x\rangle\qquad\text{for all }x\in\mathcal D.$$
--
--   Then $\{|w_x\rangle\}_{x\in\mathcal D}$ is a feasible solution to the unidirectional adversary bound for the state-conversion problem $\{(|\sigma_x\rangle,|\tau_x\rangle,O_x)\}_{x\in\mathcal D}$, i.e. $\langle w_x|((I-O_x^\dagger O_y)\otimes I_{\mathcal W})|w_y\rangle=\langle\sigma_x|\sigma_y\rangle-\langle\tau_x|\tau_y\rangle$ for all $x,y$.
--
--   This is the converse of the transducer construction of Belovs, Jeffery and Yolcu, and lets transducer constructions be analysed through adversary-bound solutions.
--
--   **Formalization Note** The catalyst $|w_x\rangle\in\mathbb C^{H\times W}$ is read in $\mathbb C^H\otimes\mathbb C^W$; "implements" is the published `TransducesWith`.
--
--   Differences from the source:
--   - encoding: Hilbert spaces V, H, W of the transducers → coordinate spaces ℂ^V over finite types; reason: Part I's transducers are finite-dimensional (pp.4, 36); the published base items use the same model
-- source:
--   Cornelissen, Apers, Gribling, Improved quantum volume estimation with transducers and amortized quantum walks, arXiv:2609.40217 (version of November 3, 2026, sha256 40d7b52d…), Theorem 2.12, p.14 (PDF p.16)

import Mathlib
import Definitions.Def_QVolTransducer_transductionComplexity
import Definitions.Def_QVolTransducer_Supplement_IsBiAdvSolution
import Definitions.Def_QVolTransducer_Supplement_UniCanonical

namespace QVolTransducer.Supplement

/-- **Catalysts of a canonical transducer are an adversary solution** (Cornelissen, Apers,
Gribling, *Improved quantum volume estimation with transducers and amortized quantum walks*,
arXiv:2609.40217 (version of November 3, 2026, sha256 40d7b52d…), Theorem 2.12, p.14 (PDF p.16)).

Let `D` be a set, `U ∈ U(V ⊕ (H ⊗ W))` and `{O_x}_{x∈D} ⊆ U(H)`. If the unidirectional canonical
transducer `T(O_x) := U(I_V ⊕ (O_x ⊗ I_W))` implements `|σ_x⟩ ⊕ |w_x⟩ ↦ |τ_x⟩ ⊕ |w_x⟩` for all
`x ∈ D`, then `{|w_x⟩}_{x∈D}` is a feasible solution to the unidirectional adversary bound for the
state-conversion problem `{(|σ_x⟩, |τ_x⟩, O_x)}_{x∈D}`.

**Formalization Note** `V, H, W` are finite index types (Part I's transducers are
finite-dimensional, p.36); "implements" is the published `QVolTransducer.TransducesWith`, and the
catalyst `|w_x⟩ ∈ ℂ^(H × W)` is read in `ℂ^H ⊗ ℂ^W` by `curryHW`. `D` is arbitrary. -/
theorem theorem_2_12 {V H W D : Type} [Fintype V] [DecidableEq V] [Fintype H] [DecidableEq H]
    [Fintype W] [DecidableEq W] (T : UniCanonical V H W) (O : D → Matrix.unitaryGroup H ℂ)
    (σ τ : D → EuclideanSpace ℂ V) (w : D → EuclideanSpace ℂ (H × W))
    (hT : ∀ x, TransducesWith (T.apply (O x)) (σ x) (τ x) (w x)) :
    IsUniAdvSolution σ τ (fun x => (O x : Matrix H H ℂ)) (fun x => curryHW (w x)) := by sorry

end QVolTransducer.Supplement
