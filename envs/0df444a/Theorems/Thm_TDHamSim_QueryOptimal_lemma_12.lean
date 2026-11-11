-- Prove2me | Theorems.Thm_TDHamSim_QueryOptimal_lemma_12
-- name    : TDHamSim.QueryOptimal.lemma_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T14:17:19.025777+00:00
-- url     : https://prove2.me/theorems/8132462d-96a9-4885-aa60-6ad5ce53eec0
-- title:
--   Lemma 12 — robust one-step amplification
-- statement:
--   Let $U,V$ be unitary, with $[V]_0=\widetilde U/2$, and define the amplification circuit as in (80). Put $\eta=\|\widetilde U-U\|$. If $\eta\le1/8$, then every unit system state satisfies
--
--   $$\|U_{\rm sim}(|0\rangle\otimes\psi)-|0\rangle\otimes U\psi\|\le3\eta.$$
--
--   The error is that of the full output state, including auxiliary leakage. This preserves both the threshold and the constant of the source lemma.
--
--   Differences from the source:
--   - encoding: qubit Hilbert spaces, tensor registers and time labels → binary-string bases, finite coordinate matrices and Fin indices with the spectral norm; reason: a change of coordinates representing every source instance, with explicit direct-sum and flag encodings
--   - generalization: the normalization-two block encoding constructed in (74)–(75) → every finite-dimensional unitary V with zero block Uapprox/2; reason: the robust amplification bound applies to every such encoding and includes the source circuit
-- source:
--   Boyang Chen, Minbo Gao, Zhengfeng Ji, Tongyang Li, Xinzhao Wang, Shuo Zhou, STOC 2027 submission #383 (October 2026), Lemma 12 — robust one-step amplification, p.31. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/383.pdf

import Definitions.Def_TDHamSim_QueryOptimal_Model

open scoped Matrix.Norms.L2Operator

namespace TDHamSim.QueryOptimal

/-- Lemma 12, p.31, generalized to every unitary normalization-two block encoding. -/
theorem lemma_12 {κ ι : Type} [Fintype κ] [Fintype ι] [DecidableEq κ] [DecidableEq ι]
    (z : κ) (V : Mat (κ × ι)) (hV : IsUnitary V) (U Uapprox : Mat ι)
    (hU : IsUnitary U) (hblock : block z V = (1/2 : ℂ) • Uapprox)
    (hη : opNorm (Uapprox-U) ≤ 1/8) :
    ∀ v : Ket ι, ‖v‖ = 1 →
      ‖act (amplify z V) (zeroIn z v) - zeroIn z (act U v)‖ ≤ 3*opNorm (Uapprox-U) := by sorry

end TDHamSim.QueryOptimal
