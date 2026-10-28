-- Prove2me | Theorems.Thm_PhaseCut_Stable_trace_split
-- name    : PhaseCut.Stable.trace_split
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-09T04:39:16.974326+00:00
-- url     : https://prove2.me/theorems/657e939a-07f9-4187-ade7-18966dc50646
-- title:
--   Proof of Lemma A.1, p. 25 — Tr V = Tr V^∥ + Tr V^⊥
-- statement:
--   Let $A \in \mathbb{C}^{n\times p}$ and $P = AA^\dagger$ the orthogonal projector onto $\mathcal{R}(A)$. For every $V \in \mathbb{C}^{n\times n}$, with $V^{/\!/} = PVP$ and $V^\perp = (I-P)V(I-P)$,
--   $$\operatorname{Tr} V = \operatorname{Tr} V^{/\!/} + \operatorname{Tr} V^\perp ,$$
--   equivalently $\operatorname{Tr} V^{/\!/} = \operatorname{Tr} V - \operatorname{Tr} V^\perp$.
--
--   In the proof of Lemma A.1 this identity, applied to the minimizer $V_{PC}$ of (13), bounds $\operatorname{Tr} V_{PC}^{/\!/}$ by $\operatorname{Tr} V_{PC} = \||Ax_0| + b_{n,PC}\|_2^2$.
--
--   **Formalization Note.** The paper states the identity for $V_{PC}$; it holds for every square matrix and is stated so.
-- source:
--   Waldspurger, d'Aspremont & Mallat, arXiv:1206.0102v3, proof of Lemma A.1, p. 25, first display

import Mathlib
import Definitions.Def_PhaseCut_Stable_Defs

namespace PhaseCut.Stable

open Matrix
open scoped ComplexOrder


/-- **Trace split**, proof of Lemma A.1 (p. 25): `Tr V = Tr V^∥ + Tr V^⊥`, i.e.
`Tr V^∥ = Tr V − Tr V^⊥`. -/
theorem trace_split {n p : ℕ} (A : Matrix (Fin n) (Fin p) ℂ) (V : Matrix (Fin n) (Fin n) ℂ) :
    V.trace = (Vpar A V).trace + (Vperp A V).trace := by sorry
end PhaseCut.Stable
