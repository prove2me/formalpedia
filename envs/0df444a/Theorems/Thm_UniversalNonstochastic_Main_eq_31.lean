-- Prove2me | Theorems.Thm_UniversalNonstochastic_Main_eq_31
-- name    : UniversalNonstochastic.Main.eq_31
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:05:33.77285+00:00
-- url     : https://prove2.me/theorems/fd6bf3a3-bf06-407a-a331-cdd769e021eb
-- title:
--   Section A.2, equation (31) — the singleton set costs only a constant
-- statement:
--   Let $K$ be prefix complexity given by an optimal prefix decoder. For some constant $c_6$,
--   $$K(\{\omega\})\le K(\omega)+c_6 \tag{31}$$
--   for every object $\omega$. Here $K(\{\omega\})$ is the complexity of the singleton finite set $\{\omega\}$, under the same finite-set coding as in the definition of stochasticity.
--
--   The inequality expresses that the computable map $\omega\mapsto\{\omega\}$ raises complexity by at most a constant. It supplies the uniform finite-model complexity comparison used for the upper bound of Theorem 1.
--
--   Differences from the source:
--   - encoding: objects ω in a basic space 𝓧 in computable bijection with ℕ → objects are positive integers ℕ+ (the paper’s ℕ = {1,2,…}), coded by themselves; reason: the source explicitly permits replacing 𝓧 by ℕ in every formal statement (p.4); ObjectEncoding and the transport functions implement its fixed computable bijection without changing any instance
--   - encoding: K: prefix complexity defined by a fixed optimal decoder → U: an arbitrary optimal conditional prefix decoder; complexity is minimal halting-program length in ℕ∞, unconditional complexity uses condition 0; reason: the source fixes any optimal decoders; ℕ∞ is the exact infimum (⊤ only on no description, which optimality excludes); every statement is quantified over all such choices before its constants
--   - encoding: some constant c6 → c₆ : ℕ; reason: both complexities are integers, so a real constant can be replaced by its ceiling; same statement
-- source:
--   Vladimir Vovk, The universal measure of nonstochastic objects, STOC 2027 submission #11 (October 2026), SHA-256 1ca25c4b7c38d8f49718c9fecbc2a434a7592886b44992c4fbef31ab3f480078, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/11.pdf, Sect. A.2, eq. (31), p.17 (PDF p.17)

import Mathlib
import Definitions.Def_UniversalNonstochastic_Main_Complexity

namespace UniversalNonstochastic.Main

/-- Section A.2, equation (31), p.17: for some constant `c₆`, `K({ω}) ≤ K(ω) + c₆` for every
object `ω`; `K({ω})` is the prefix complexity of the code of the finite set `{ω}`. -/
theorem eq_31 (U : OptimalPrefixDecoder) :
    ∃ c₆ : ℕ, ∀ ω : ℕ+, Kset U {ω} ≤ Kobj U ω + c₆ := by sorry

end UniversalNonstochastic.Main
