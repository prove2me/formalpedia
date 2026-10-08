-- Prove2me | Theorems.Thm_QuantumWalkSearch_ApproxRAA_lemma_2
-- name    : QuantumWalkSearch.ApproxRAA.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T08:44:39.664823+00:00
-- url     : https://prove2.me/theorems/e5c43b9e-4374-49c8-ab56-4921a5e09df1
-- title:
--   Lemma 2 — Tolerant RAA(t_max, γ) never succeeds when M is empty and ends with a marked element with probability ≥ 1/12 − 3γ otherwise
-- statement:
--   Let $|\pi\rangle\in\mathcal H=\mathbb C^{X\times X}$ be a unit vector, $M\subseteq X$ a marked set and $p_M=\|\Pi_M|\pi\rangle\|^2$. Let $0<\gamma\le1/40$, and for $i\ge1$ let $R_i$ be a unitary on $\mathcal H\otimes K_i$ with
--
--   1. $R_i|\pi\rangle|0\rangle=|\pi\rangle|0\rangle$, and
--   2. $\|(R_i+\mathrm{Id})|\psi\rangle|0\rangle\|\le\beta_i\|\psi\|$ for every $|\psi\rangle\perp|\pi\rangle$, where $\beta_i=\frac{18}{4\pi^3}\frac{\gamma}{i^2}$.
--
--   Let $\varepsilon>0$ be such that $p_M\ge\varepsilon$ whenever $p_M>0$, and let $t_{\max}$ be the smallest non-negative integer such that $3^{t_{\max}}\sin^{-1}\sqrt\varepsilon\in[\pi/4,3\pi/4]$. Then the probability $P_{\rm succ}$ that Tolerant RAA$(t_{\max},\gamma)$ ends with a marked element satisfies
--   $$
--   M=\emptyset\ \Longrightarrow\ P_{\rm succ}=0,\qquad\qquad p_M>0\ \Longrightarrow\ P_{\rm succ}\ \ge\ \frac1{12}-3\gamma .
--   $$
--
--   This is the search procedure behind the paper's Theorem 3: only a lower bound $\varepsilon$ on $p_M$ is known, the number of levels is guessed by trying every $i\le t_{\max}$ in turn on the state left over from the previous failed attempt, and the reflection about $|\pi\rangle$ is available only approximately.
--
--   **Formalization Note** "Always outputs No marked element if $M$ is empty" is the statement that the success probability is $0$; the success probability is defined from the measurement rule of the procedure (see the Tolerant RAA module). The paper's "$M$ non-empty" is read as $p_M>0$, as in its proof ("we now assume that $M$ is non-empty and $p_M\ge\varepsilon$"): a marked set on which $|\pi\rangle$ has no weight cannot be found by this procedure. The cost clause ("incurs a cost of order $3^{t_{\max}}(c_1\log1/\gamma+c_2)$") and property 1 of $R(\beta)$ are not formalized. The circuits are required only at the precisions $\beta_1,\beta_2,\dots$.
-- source:
--   Magniez, Nayak, Roland, Santha, Search via Quantum Walk, arXiv:quant-ph/0608026v4, p. 15, Lemma 2 (proof pp. 15–17)

import Mathlib
import Definitions.Def_QuantumWalkSearch_ApproxRAA_Setting
import Definitions.Def_QuantumWalkSearch_ApproxRAA_Circuit
import Definitions.Def_QuantumWalkSearch_ApproxRAA_Tolerant

namespace QuantumWalkSearch.ApproxRAA

/-- Lemma 2 (p. 15), exact half. Let `ε > 0` with `p_M ≥ ε` whenever `p_M > 0`, and let
`t_max` be the smallest non-negative integer with `3^{t_max} sin⁻¹ √ε ∈ [π/4, 3π/4]`. For every
`0 < γ ≤ 1/40`, if the circuits `R i` satisfy properties 2–3 at `β_i = 18γ/(4π³ i²)`, then
Tolerant RAA(t_max, γ) ends with a marked element with probability `0` if `M` is empty, and
with probability at least `1/12 − 3γ` if `p_M > 0`. (The cost clause is not formalized.) -/
theorem lemma_2 {X : Type*} [Fintype X] [DecidableEq X] {κ : ℕ → Type*}
    [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)]
    (M : Finset X) (piState : EuclideanSpace ℂ (X × X)) (hπ : ‖piState‖ = 1)
    (z : ∀ i, κ i) (R : ∀ i, Matrix (X × X × κ i) (X × X × κ i) ℂ)
    (γ : ℝ) (hγ : 0 < γ) (hγ' : γ ≤ 1 / 40) (hR : ApproxReflections piState z R γ)
    (ε : ℝ) (hε : 0 < ε) (hεp : 0 < markedWeight M piState → ε ≤ markedWeight M piState)
    (tmax : ℕ) (htmax : IsFirstHit (Real.arcsin (Real.sqrt ε)) tmax) :
    (M = ∅ → successProb M z R piState tmax = 0) ∧
      (0 < markedWeight M piState → 1 / 12 - 3 * γ ≤ successProb M z R piState tmax) := by sorry

end QuantumWalkSearch.ApproxRAA
