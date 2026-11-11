-- Prove2me | Theorems.Thm_QuadStatRE_Main_lemma_3_2
-- name    : QuadStatRE.Main.lemma_3_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T22:47:06.394229+00:00
-- url     : https://prove2.me/theorems/841126bf-6ba4-4b73-b874-f37efa9196d4
-- title:
--   Lemma 3.2 — the basic gadget is perfectly simulable from f(v) and the equality leakage W_{0,s}
-- statement:
--   Let $t\ge1$. The basic encoding $\mathrm{Enc}_t$ of $f(x,y,z,w)=xyz+w$ (Construction 1) is a leaky randomized encoding of $f$ with leakage $W_{0,s}$, $s=(x,y,z)$, and simulation error $0$: there is a randomized algorithm $\mathrm{Sim}_{\mathrm{leak}}$, using uniform coins independent of the leakage sample, such that for every input $v=(x,y,z,w)$
--   $$\mathrm{SD}\big(\mathrm{Enc}_t(v),\ \mathrm{Sim}_{\mathrm{leak}}(f(v),W_{0,(x,y,z)})\big)=0.$$
--   Here $W_{0,s}$ reveals a uniform $V\in\mathbb F_2^3$ and the flag $\mathbf 1[V=s]$.
--
--   The lemma identifies exactly what the gadget leaks beyond $f(v)$: one equality test. All later privacy analysis tracks this leakage.
--
--   **Formalization Note.** "Leaky encoding with leakage $L$" is `HasLeakage … 0` (Definition 2.3 with $\varepsilon=0$); the simulator is a deterministic map of $(f(v),\text{leakage},\text{coin bits})$.
--
--   Differences from the source:
--
--   - encoding: randomized algorithm Sim_leak with internal randomness independent of the leakage sample → a deterministic map of (f(v), leakage sample, τ uniform coin bits), output law the mixture over the leakage; reason: a randomized algorithm with a uniform tape
--   - encoding: SD = 0 between the encoding and the simulation → HasLeakage with ε = 0, i.e. SD ≤ 0; reason: SD is nonnegative, so ≤ 0 is = 0
--   - encoding: bits {0,1} and F₂ → ZMod 2; reason: the same field
-- source:
--   Applebaum, Quadratic Statistical Randomized Encoding for All Functions, STOC 2027 submission (manuscript sha256 000cbf4e…), p. 18, Lemma 3.2

import Mathlib
import Definitions.Def_QuadStatRE_Main_BasicEncoding
import Definitions.Def_QuadStatRE_Main_LeakyEncoding
import Definitions.Def_QuadStatRE_Main_LeakageFamily
open QuadraticRE

namespace QuadStatRE.Main

/-- Lemma 3.2 (Exact leaky simulation), p. 18: for every `t ≥ 1`, the basic encoding is a leaky
randomized encoding of `f(x, y, z, w) = xyz + w` with leakage `W_{0,s}`, `s = (x, y, z)`, and
simulation error `0`. -/
theorem lemma_3_2 (t : ℕ) (ht : 1 ≤ t) :
    HasLeakage targetF (basicDesc t).eval (fun v => W0 (secretOf v)) 0 := by sorry

end QuadStatRE.Main
