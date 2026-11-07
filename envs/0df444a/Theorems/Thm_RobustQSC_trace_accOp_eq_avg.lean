-- Prove2me | Theorems.Thm_RobustQSC_trace_accOp_eq_avg
-- name    : RobustQSC.trace_accOp_eq_avg
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T20:50:12.317262+00:00
-- url     : https://prove2.me/theorems/1913cdf9-ab26-413b-ba35-20a291fbe0a5
-- title:
--   §4, p.21 — $\mathrm{Tr}[A_f|g\rangle\langle g|]=\frac12\mathrm{Avg}_f[g]+\frac12\mathrm{Avg}_{\hat f}[\hat g]$
-- statement:
--   Let $|\hat f\rangle=H^{\otimes n}|f\rangle$ and $|\hat g\rangle=H^{\otimes n}|g\rangle$. Then
--
--   $$
--   \mathrm{Tr}[A_f|g\rangle\langle g|]=\frac12\mathrm{Avg}_f[g]+\frac12\mathrm{Avg}_{\hat f}[\hat g].
--   $$
--
--   The two terms are the $Z$-basis and the $X$-basis tests. This rewriting is what turns soundness into an uncertainty principle.
--
--   Differences from the source:
--   - generalization: $f$, $g$ a target and a pure lab state → all vectors $f,g$ and all $n$; reason: the proof uses no normalization: each fibre of $f$ is normalized inside $A_f$, and both sides vanish on zero fibres and at $n=0$; the printed claim is the case of unit vectors
--   - encoding: $\mathrm{Tr}[A_f|g\rangle\langle g|]$ → `effectProb (accOp f) (pureDensity g)`, the real part of the trace; reason: $A_f$ is Hermitian, so the trace is real; same quantity
-- source:
--   Coladangelo, Li, Slote, Robust quantum state certification and uncertainty principles for total influence, arXiv:2607.27184 (sha256 09d2692e…), §4, p.21

import Definitions.Def_RobustQSC_accOp
import Definitions.Def_RobustQSC_avg

namespace RobustQSC

open QAlgorithms

/-- **§4, the Avg rewriting (p.21).** With `|f̂⟩ = H^{⊗n}|f⟩` and `|ĝ⟩ = H^{⊗n}|g⟩`,
`Tr[A_f|g⟩⟨g|] = ½ Avg_f[g] + ½ Avg_f̂[ĝ]`.

Source: Coladangelo, Li, Slote, *Robust quantum state certification and uncertainty principles for
total influence*, arXiv:2607.27184 (sha256 09d2692e…), §4, p.21 ("It is straightforward to verify that we can rewrite Tr[A_f|g⟩⟨g|] as
½Avg_f[g] + ½Avg_f̂[ĝ], where Avg_f[g] := … , Avg_f̂[ĝ] := …").

**Formalization Note.** Stated for all vectors `f`, `g` (both sides are invariant under scaling
each fiber of `f`, and both vanish on zero fibers); the paper's target state and pure lab state are
the case of unit vectors. -/
theorem trace_accOp_eq_avg (n : ℕ) (f g : EuclideanSpace ℂ (Qubits n)) :
    effectProb (accOp f) (pureDensity g) = avg f g / 2 + avg (fourier f) (fourier g) / 2 := by sorry

end RobustQSC
