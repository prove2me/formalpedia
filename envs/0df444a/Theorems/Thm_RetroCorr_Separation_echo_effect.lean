-- Prove2me | Theorems.Thm_RetroCorr_Separation_echo_effect
-- name    : RetroCorr.Separation.echo_effect
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T09:27:19.686524+00:00
-- url     : https://prove2.me/theorems/40a2c8d2-70f2-4c83-83fe-a94d15a929f3
-- title:
--   §3, p. 3 — echo effect: on the maximally entangled state, measuring the reference in B^T and the control in B gives equal outcomes, P(i, j) = δ_ij / c
-- statement:
--   Let $c\ge1$, let $W\in U(c)$ be a unitary with columns $w_1,\dots,w_c$ (the basis $B$), and let $\Phi_c=c^{-1/2}\sum_{a}|a\rangle_{\mathrm{ref}}|a\rangle_{\mathrm{ctrl}}$ be the maximally entangled state of a reference system and the control. Measure the reference in the basis $B^T$, whose projectors are $(|w_i\rangle\langle w_i|)^T=|\bar w_i\rangle\langle\bar w_i|$, and the control in the basis $B$. Then for all $i,j$,
--   $$\Pr[\text{reference gives } i,\ \text{control gives } j]=\operatorname{Tr}\!\Big[\big((|w_i\rangle\langle w_i|)^T\otimes|w_j\rangle\langle w_j|\big)\,|\Phi_c\rangle\langle\Phi_c|\Big]=\begin{cases}1/c,& i=j,\\ 0,& i\ne j.\end{cases}$$
--
--   So the two outcomes always agree: the measurement of the other half of the entangled pair in $B^T$ reproduces ("echoes") the result $j$ of the channel's measurement of the control in $B$, whatever $B$ is. This is the identity behind the protocol of Fig. 2.
--
--   **Formalization Note** The projectors are `transposeBasisProj W i` and `basisProj W j`, the state is `maxEntDensity c` on `Fin c × Fin c` (reference first), and the probability is `QAlgorithms.effectProb` (the real part of the trace). For $c=0$ there are no outcomes and the statement is empty.
--
--   Differences from the source:
--   - generalization: the control is a qubit and the pair an ebit (c = 2) → every c, with the maximally entangled state Φ_c; reason: at c = 2 it is the paper's statement
--   - reading: "measure the other half in the basis B^T" → the projectors (|w_i⟩⟨w_i|)^T = |w̄_i⟩⟨w̄_i|; reason: B^T is the basis of transposed projectors of B
--   - reading: "creating an echo of the measurement result j" → the joint outcome law of the B^T measurement on the reference and the B measurement on the control is δ_ij / c; reason: perfect correlation of the two outcomes is the echo
--   - encoding: basis B, outcomes 1…c → columns of a unitary W, outcomes in Fin c (0-based); reason: Lean convention; same bases
-- source:
--   Bennett, Devetak, Shor & Smolin, Inequalities and separations among assisted capacities of quantum channels, arXiv:quant-ph/0406086v1, p. 3, §3 ("The essential trick …")

import Mathlib
import Definitions.Def_RetroCorr_Separation_Channel

namespace RetroCorr.Separation
theorem echo_effect (c : ℕ) (W : Matrix.unitaryGroup (Fin c) ℂ) (i j : Fin c) :
    QAlgorithms.effectProb (Matrix.kronecker (transposeBasisProj W i) (basisProj W j))
      (maxEntDensity c) = if i = j then ((c : ℝ))⁻¹ else 0 := by sorry
end RetroCorr.Separation
