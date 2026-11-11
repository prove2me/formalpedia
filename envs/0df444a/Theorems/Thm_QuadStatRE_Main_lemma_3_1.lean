-- Prove2me | Theorems.Thm_QuadStatRE_Main_lemma_3_1
-- name    : QuadStatRE.Main.lemma_3_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T22:45:53.323392+00:00
-- url     : https://prove2.me/theorems/68cc9778-ec91-45f4-820b-73a2606928f2
-- title:
--   Lemma 3.1 — the basic gadget has 7 + t outputs, 6 + 3t random bits, degree ≤ 2 and correctness error exactly (7/8)2^{−t}
-- statement:
--   Let $t\ge1$ and let $\mathrm{Enc}_t:\mathbb F_2^4\times\mathbb F_2^{6+3t}\to\mathbb F_2^{7+t}$ be the basic encoding of $f(x,y,z,w)=xyz+w$ (Construction 1), with its decoder $\mathrm{Dec}_t$. Then $\mathrm{Enc}_t$ has $7+t$ output bits, uses $6+3t$ random bits, every output bit is a polynomial of total degree at most two in the input and random bits jointly, and for every input $v\in\mathbb F_2^4$
--   $$\Pr_{r\leftarrow\mathbb F_2^{6+3t}}\big[\mathrm{Dec}_t(\mathrm{Enc}_t(v;r))\ne f(v)\big]=\delta_t=\tfrac78\,2^{-t}.$$
--
--   This is the starting point of the construction: a quadratic gadget whose correctness error is as small as desired, at the price of a constant privacy error.
--
--   **Formalization Note.** The output and randomness lengths are the type $\mathbb F_2^4\times\mathbb F_2^{6+3t}\to\mathbb F_2^{7+t}$ of the description; degree is the published `Desc.DegLE 2` (every monomial has at most two variables); probabilities are uniform counts over tapes.
--
--   Differences from the source:
--
--   - encoding: 7 + t output bits, 6 + 3t random bits → the type Desc 4 (6 + 3t) (7 + t) of basicDesc t; reason: the lengths are fixed by the construction; stating them as the type is the same claim
--   - encoding: total degree at most two in (v, r) jointly → Desc.DegLE 2 of the description (3.1)–(3.2); reason: the published degree notion, joint in input and tape variables
--   - encoding: correctness error Pr[Dec(Enc(v)) ≠ f(v)] → prob over the uniform tape Fin (6 + 3t) → ZMod 2; reason: uniform probability as a counting ratio
--   - encoding: bits {0,1} and F₂ → ZMod 2; reason: the same field
-- source:
--   Applebaum, Quadratic Statistical Randomized Encoding for All Functions, STOC 2027 submission (manuscript sha256 000cbf4e…), p. 17, Lemma 3.1

import Mathlib
import Definitions.Def_QuadraticRE_Desc
import Definitions.Def_QuadraticRE_SD
import Definitions.Def_QuadStatRE_Main_BasicEncoding
open QuadraticRE

namespace QuadStatRE.Main

/-- Lemma 3.1 (Basic correctness), p. 17: for every `t ≥ 1`, Construction 1 has `7 + t` output bits
and `6 + 3t` random bits (its type), total degree at most two jointly in the input and the random bits,
and correctness error exactly `δ_t = (7/8) 2^{-t}` for every input. -/
theorem lemma_3_1 (t : ℕ) (ht : 1 ≤ t) :
    (basicDesc t : Desc 4 (6 + 3 * t) (7 + t)).DegLE 2 ∧
      ∀ v : Fin 4 → F2,
        prob (fun r : Fin (6 + 3 * t) → F2 => basicDec t ((basicDesc t).eval v r) ≠ some (targetF v))
          = 7 / 8 * (1 / 2 : ℝ) ^ t := by sorry

end QuadStatRE.Main
