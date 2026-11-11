-- Prove2me | Theorems.Thm_QuantumSymmetryBreaking_CycleColoring_lemma_4_1
-- name    : QuantumSymmetryBreaking.CycleColoring.lemma_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T21:26:08.519559+00:00
-- url     : https://prove2.me/theorems/4cde6fd7-3b01-48ed-9749-5bbb53b97b7c
-- title:
--   Lemma 4.1 — $\|[e,e]-\sum_i(K_{+i}W^2K_{+i}+K_{-i}W^2K_{-i})\|_F\le(2s+1)\lambda^n$
-- statement:
--   Let $s\ge10^4$. Every $K_{\pm i}=\frac14([e,e]\pm[i,e])([e,e]\mp[e,i])$ ($i\in[s]$) is self-adjoint, and there is a real number $\lambda<1$ such that for every $n\ge1$ there exists a self-adjoint $W\in\mathbb C[G\times G]$ with
--   $$
--   \Bigl\|[e,e]-\sum_{i}\bigl(K_{+i}W^2K_{+i}+K_{-i}W^2K_{-i}\bigr)\Bigr\|_F\le(2s+1)\lambda^n .
--   $$
--   This is the key lemma of §4: a family of $2s$ positive group-algebra elements of zero "energy" that sums to approximately the identity, which §5 realizes with finite matrices.
--
--   Differences from the source:
--   - reading: “$\|\cdots\|\le\lambda^n$ for some $\lambda<1$” for every $n\ge1$ → one $\lambda<1$ chosen before $n$, the bound holding for every $n\ge1$; reason: $\lambda$ is the constant $3/4+24/\sqrt{2s}$ of Lemma 4.5 (proof of Lemma 4.3, p.14); a $\lambda$ depending on $n$ would make the bound vacuous
--   - encoding: generators indexed by $[s]=\{1,\dots,s\}$ → generators indexed by `Fin s` = $\{0,\dots,s-1\}$; reason: relabelling only
--   - encoding: $G=\langle g_1,\dots,g_s\mid g_i^2=e\rangle$ with word length $|g|$ → the universal Coxeter group on `Fin s` (Coxeter matrix with off-diagonal entries 0, Mathlib's encoding of $\infty$) with its Coxeter length; reason: the same presentation; Coxeter length is the reduced-word length
-- source:
--   Flin, Li, Suomela, Quantum Advantage for Distributed Symmetry Breaking, STOC 2027 submission #863 (October 2026), source.pdf SHA-256 121c1ecfd6ed3365b5424f6f5978549d12510d800fb87cb8d2f5e110600a542e, Lemma 4.1, p.12 (PDF p.15)

import Mathlib
import Definitions.Def_QuantumSymmetryBreaking_CycleColoring_GroupAlgebra

namespace QuantumSymmetryBreaking.CycleColoring

/-- Lemma 4.1, Flin, Li, Suomela, *Quantum Advantage for Distributed Symmetry Breaking*, STOC 2027 submission #863 (October 2026), p.12 (PDF p.15).
For `s ≥ 10^4`, every `K_{±i}` is self-adjoint, and there is a real `λ < 1` (fixed before `n`) such that
for every `n ≥ 1` some self-adjoint `W ∈ ℂ[G × G]` satisfies
`‖[e,e] − ∑_i (K_{+i} W^2 K_{+i} + K_{-i} W^2 K_{-i})‖_F ≤ (2s + 1) λ^n`. -/
theorem lemma_4_1 (s : ℕ) (hs : 10 ^ 4 ≤ s) :
    (∀ i : Fin s, IsSelfAdj (Kplus i) ∧ IsSelfAdj (Kminus i)) ∧
    ∃ c : ℝ, c < 1 ∧ ∀ n : ℕ, 1 ≤ n → ∃ W : Alg s, IsSelfAdj W ∧
      algFrob (br 1 1 - ∑ i : Fin s, (Kplus i * W ^ 2 * Kplus i + Kminus i * W ^ 2 * Kminus i)) ≤
        (2 * s + 1) * c ^ n := by sorry

end QuantumSymmetryBreaking.CycleColoring
