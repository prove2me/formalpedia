-- Prove2me | Theorems.Thm_ShiSpread_runLayered_embedCirc_spread
-- name    : ShiSpread.runLayered_embedCirc_spread
-- status  : Proved
-- author  : @Goku
-- created : 2026-09-11T08:38:40.983652+00:00
-- url     : https://prove2.me/theorems/8458ef72-fc8e-4851-a34e-54082641edd2
-- title:
--   Wire relabelling commutes with running a whole layered circuit on a zero-padded state
-- statement:
--   For an injective wire embedding $e$ and a layered circuit $c$ on $m$ wires,
--
--   $$\\mathrm{runLayered}\\big(\\mathrm{embedCirc}_e(c)\\big)\\big(\\mathrm{spread}_e\\,\\psi\\big)=\\mathrm{spread}_e\\big(\\mathrm{runLayered}(c)\\,\\psi\\big).$$
--
--   This is the semantic content the purely syntactic relabelling bundle deliberately left unproved: the state extension $\\mathrm{spread}_e$ INTERTWINES a circuit with its relabelled copy, so a circuit run on a fresh zero-initialised register behaves exactly as the same circuit on the smaller register. It is the prerequisite for placing circuits side by side and for running repeated copies, which is what error amplification needs.
--
--   Proved by a double induction (layers, then instructions within a layer) citing the published single-instruction transport law as a tracked reduction. Both levels are `List.foldl`, so the accumulator changes as the induction proceeds and the state must be generalised at each level.
--
--   **Injectivity is required, not cosmetic.** `embedLayer`/`embedCirc` need it for the `cnot` constructor, and for non-injective $e$ the map $\\mathrm{spread}_e$ is not the amplitude array of any $\\psi\\otimes|0\\cdots0\\rangle$ at all — it discards the components of $\\psi$ at basis strings differing within a fibre of $e$ — so the statement would not carry its intended meaning.
--
--   **Off-image wires are pinned to $|0\\rangle$.** This is transport for a ZERO-INITIALISED register — the situation parallel composition and repetition need — and does NOT model an arbitrary or entangled environment state; nothing extends to mixed states. Relatedly $\\mathrm{spread}_e$ realises the intended tensor only up to the wire permutation induced by $e$, and when $e$ is surjective (in particular $m=n$) there is no zero register at all.
--
--   **$\\mathrm{acceptProb}$ transport is NOT proved**, here or anywhere yet. It needs two further lemmas: compatibility between $\\mathrm{spread}$ and $\\mathrm{inputState}$ for the canonical inclusion (false for non-canonical $e$, where the spread input state is permuted), and a reindexing of the defining sum using that $\\mathrm{spread}$ vanishes off its support. So nothing about acceptance probabilities, $\\mathrm{outDist}$ or induced matrices follows from this. Nothing here concerns two circuits on disjoint images commuting, and no linearity, injectivity or norm-preservation of $\\mathrm{spread}_e$ is claimed.

import Definitions.Def_ShiSpread_Core

namespace ShiSpread

open ShiEmbed ShiShallow in
/-- **The semantic transport law for wire relabelling.** Running a relabelled circuit on an
extended state equals extending the result of running the original circuit. Requires `e`
injective. Because `spread` pins every wire off the image of `e` to `|0⟩`, this is transport
for a zero-initialised register, NOT an arbitrary environment. Statement about `runLayered`
only: nothing about `acceptProb`, `outDist`, or circuits on disjoint images commuting. -/
theorem runLayered_embedCirc_spread {m n : ℕ} (e : Fin m → Fin n) (he : Function.Injective e)
    (c : Layered m) (ψ : QState m) :
    runLayered (embedCirc e he c) (spread e ψ) = spread e (runLayered c ψ) := by sorry

end ShiSpread
