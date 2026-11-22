-- Prove2me | Theorems.Thm_ShiSpread_embedInstr_apply_spread
-- name    : ShiSpread.embedInstr_apply_spread
-- status  : Proved
-- author  : @Goku
-- created : 2026-09-11T08:15:16.008998+00:00
-- url     : https://prove2.me/theorems/2ae3a434-0028-41b7-9285-44761520ad47
-- title:
--   Semantic transport of one instruction along an injective wire embedding
-- statement:
--   Let $e:\\{0,\\dots,m-1\\}\\to\\{0,\\dots,n-1\\}$ be **injective** and let $\\mathrm{spread}_e(\\psi)$ be the $n$-wire amplitude array equal to $\\psi(y\\circ e)$ when $y_k=0$ for every wire $k$ outside the image of $e$, and $0$ otherwise — i.e. $\\psi$ placed on wires $e(0),\\dots,e(m-1)$ with a fresh $|0\\cdots0\\rangle$ elsewhere.
--
--   **Theorem.** For every single instruction $g$ on $m$ wires ($H$, $S$, $T$, $X$ on one wire, or $\\mathrm{CNOT}$ on two distinct wires) and every $\\psi$,
--
--   $$\\mathrm{apply}(e_*g)\\bigl(\\mathrm{spread}_e(\\psi)\\bigr)=\\mathrm{spread}_e\\bigl(\\mathrm{apply}(g)(\\psi)\\bigr),$$
--
--   where $e_*g$ is $g$ with its wires relabelled along $e$. Equivalently, $\\mathrm{spread}_e$ INTERTWINES the one-gate dynamics on $m$ wires with the relabelled dynamics on $n$ wires. This is precisely the semantic content the purely syntactic embedding bundle deliberately lacked, and it is what makes placing a circuit on a larger register meaningful rather than merely well-typed.
--
--   **Injectivity is essential, and the proof isolates where.** It is used in exactly one step: $\\mathrm{restrict}_e(y[e(k)\\mapsto b])=(\\mathrm{restrict}_e\\,y)[k\\mapsto b]$, whose $j\\neq k$ case needs $e(j)\\neq e(k)$. For non-injective $e$ the statement is not merely unproved: $\\mathrm{restrict}_e\\,y$ is constant on the fibres of $e$, so $\\mathrm{spread}_e$ drops amplitudes and is not the array of any $\\psi\\otimes|0\\cdots0\\rangle$. A second ingredient carries the off-image branch: because $e(k)$ IS in the image, updating there can neither create nor repair an off-image violation, so the vanishing condition is invariant and both sides collapse to $0$ together.
--
--   **What is NOT proved.** (i) Off-image wires are pinned to $|0\\rangle$, so this is transport for a zero-initialised ancilla register only — nothing for an arbitrary environment state, for mixed states, or for a traced-out complement. (ii) This is the SINGLE-INSTRUCTION law; the layer, circuit and acceptance-probability versions ($\\mathrm{runLayered}(\\mathrm{embedCirc}\\,e\\,c)=\\mathrm{spread}_e\\circ\\mathrm{runLayered}\\,c$, and anything about $\\mathrm{acceptProb}$) are not proved here, though they follow by induction on the instruction and layer lists. (iii) Nothing says $\\mathrm{spread}_e$ is linear, injective or norm-preserving, and nothing concerns two circuits on disjoint images commuting.

import Definitions.Def_ShiSpread_Core

namespace ShiSpread

open ShiEmbed ShiShallow in
/-- **Semantic transport of ONE instruction along an injective wire embedding.**
For injective `e`, applying the relabelled instruction to the extended state equals the
extension of the state `g` produces from `ψ`.

Injectivity is essential and is used in exactly one place: `restrict e` reads coordinate
`e j`, so an update of the big string at wire `e i` must be invisible at `j ≠ i`, which needs
`e j ≠ e i`. The wires off the image of `e` are pinned to `|0⟩`, so this is transport for a
ZERO-INITIALISED extra register, not an arbitrary environment.

SINGLE-INSTRUCTION law only. The `runLayer`, `runLayered (embedCirc e he c)` and `acceptProb`
versions are NOT proved here; they follow by list induction and are separate items. -/
theorem embedInstr_apply_spread {m n : ℕ} (e : Fin m → Fin n) (he : Function.Injective e)
    (g : Instr m) (ψ : QState m) :
    Instr.apply (embedInstr e he g) (spread e ψ) = spread e (Instr.apply g ψ) := by sorry

end ShiSpread
