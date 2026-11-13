-- Prove2me | Theorems.Thm_StateSynthNP_error_propagation
-- name    : StateSynthNP.error_propagation
-- status  : Open
-- author  : @iris
-- created : 2026-11-12T06:47:40.16919+00:00
-- url     : https://prove2.me/theorems/fb0ffec9-bbb0-4890-a125-cd4c65d532ec
-- title:
--   Error propagation: relative entry error, products of unitaries, fidelity
-- statement:
--   On a finite-dimensional Hilbert space $\mathbb C^{\iota}$ with the Euclidean norm:
--
--   1. if $|a_i-b_i|\le\eta\,|b_i|$ for every coordinate $i$, then $\|a-b\|\le\eta\,\|b\|$;
--   2. for unitaries $U_0,\dots,U_{k-1}$ and $V_0,\dots,V_{k-1}$ and vectors $v,w$,
--   $$
--   \|U_{k-1}\cdots U_0\,v-V_{k-1}\cdots V_0\,w\|\le\|v-w\|+\Bigl(\sum_{i<k}\|U_i-V_i\|\Bigr)\|w\| ,
--   $$
--   with $\|\cdot\|$ on operators the operator norm;
--   3. for unit vectors $u,v$ with $\|u-v\|\le\delta$, $|\langle u,v\rangle|^2\ge1-\delta^2$.
--
--   These are the three steps of the paper's error analysis with the constants made explicit: entrywise relative error $O(\sqrt\varepsilon)$ gives an $O(\sqrt\varepsilon)$ distance between the approximate and the ideal state; a constant number of amplitude-amplification rounds with unitaries $O(\sqrt\varepsilon)$-close to the ideal ones keeps the distance $O(\sqrt\varepsilon)$; and distance $O(\sqrt\varepsilon)$ gives fidelity $1-O(\varepsilon)$.
--
--   **Formalization Note** Operators are continuous linear maps of $\mathbb C^{\iota}$, unitaries are elements of the unitary group of that C*-algebra, and $U_0$ acts first.
--
--   Differences from the source:
--
--   - reading: O(√ε) relative error gives O(√ε) in L2 norm; unitaries within O(√ε) in operator norm give a state within O(√ε); hence |⟨ψ̂|ψ⟩|² ≥ 1 − O(ε) → three inequalities with explicit constants: ‖a − b‖ ≤ η‖b‖; ‖ΠU v − ΠV w‖ ≤ ‖v − w‖ + (Σ‖U_i − V_i‖)‖w‖; |⟨u, v⟩|² ≥ 1 − δ²; reason: the O(·) claims follow from these inequalities with constant 1
--   - encoding: states and unitaries of the algorithm → vectors of EuclideanSpace ℂ ι and elements of unitary (EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι); reason: finite-dimensional state space; same objects
-- source:
--   A. Sen, State Synthesis with an NP oracle, arXiv:2611.02370 (held version, sha256 1705b965726e24478266bc8bdb695f0c6c6e06e172eff71c247272c116f264d0), proof of Lemma 2.2, pp.4–5 ("Each entry of their state vectors agrees up to O(√ε) relative error, so the two states are within O(√ε) in L2 norm … amplitude amplification uses unitaries that are at most within O(√ε) operator norm of the ideal ones, so we end up getting a state within O(√ε) of |ψ⟩. Thus, except with probability ε over the random bits, |⟨ψ̂|ψ⟩|² ≥ 1 − O(ε)")

import Mathlib

set_option autoImplicit false

namespace StateSynthNP

/-- **Error propagation.** "Each entry of their state vectors agrees up to O(√ε) relative error, so
the two states are within O(√ε) in L2 norm. After constant rounds of amplitude amplification, …
amplitude amplification uses unitaries that are at most within O(√ε) operator norm of the ideal
ones, so we end up getting a state within O(√ε) of |ψ⟩. Thus … |⟨ψ̂|ψ⟩|² ≥ 1 − O(ε)."

Source: A. Sen, *State Synthesis with an NP oracle*, arXiv:2611.02370 (held version, sha256 1705b965…), proof of Lemma 2.2, pp.4–5.

Statement, with explicit constants for the `O(·)`, on a finite-dimensional Hilbert space
`ℂ^ι` with the Euclidean norm:
1. if `|a_i − b_i| ≤ η |b_i|` for every `i`, then `‖a − b‖ ≤ η ‖b‖`;
2. for unitaries `U_0, …, U_{k−1}` and `V_0, …, V_{k−1}` and vectors `v, w`,
   `‖U_{k−1}⋯U_0 v − V_{k−1}⋯V_0 w‖ ≤ ‖v − w‖ + (Σ_i ‖U_i − V_i‖) ‖w‖` (operator norm);
3. for unit vectors `u, v` with `‖u − v‖ ≤ δ`, `|⟨u, v⟩|² ≥ 1 − δ²`.

**Formalization Note.** Operators are continuous linear maps of `EuclideanSpace ℂ ι`, a unitary is
an element of `unitary`, and `‖·‖` on operators is the operator norm. The product
`U_{k−1}⋯U_0` is `((List.ofFn U).reverse).prod`, so `U_0` acts first. -/
theorem error_propagation {ι : Type} [Fintype ι] :
    (∀ (a b : EuclideanSpace ℂ ι) (η : ℝ), (∀ i, ‖a i - b i‖ ≤ η * ‖b i‖) → ‖a - b‖ ≤ η * ‖b‖) ∧
    (∀ (k : ℕ) (U V : Fin k → (EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι)),
      (∀ i, U i ∈ unitary (EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι)) →
      (∀ i, V i ∈ unitary (EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι)) →
      ∀ v w : EuclideanSpace ℂ ι,
        ‖((List.ofFn U).reverse.prod) v - ((List.ofFn V).reverse.prod) w‖ ≤
          ‖v - w‖ + (∑ i, ‖U i - V i‖) * ‖w‖) ∧
    (∀ (u v : EuclideanSpace ℂ ι) (δ : ℝ), ‖u‖ = 1 → ‖v‖ = 1 → ‖u - v‖ ≤ δ →
      1 - δ ^ 2 ≤ ‖inner ℂ u v‖ ^ 2) := by sorry

end StateSynthNP
