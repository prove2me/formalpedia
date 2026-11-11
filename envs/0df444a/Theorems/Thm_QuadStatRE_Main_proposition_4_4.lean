-- Prove2me | Theorems.Thm_QuadStatRE_Main_proposition_4_4
-- name    : QuadStatRE.Main.proposition_4_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T22:46:55.853262+00:00
-- url     : https://prove2.me/theorems/8e403b0f-4bd2-43a1-81a2-19b00c9ec8cc
-- title:
--   Proposition 4.4 — amplification has leakage A(W) with error ≤ 15ε, and A preserves affine symmetry
-- statement:
--   Let $E$ be an encoding of $f(x,y,z,w)=xyz+w$ and $W=(W_s)_{s\in G}$ a family of distributions on a finite alphabet $\Omega$. If $E$ has leakage family $W$ with leakage error $\varepsilon$, i.e.
--   $$\mathrm{SD}\big(\mathrm{Enc}_E(v),\ \mathrm{Sim}_{\mathrm{leak}}(f(v),W_{(x,y,z)})\big)\le\varepsilon\quad\text{for every } v=(x,y,z,w),$$
--   then its amplification (Construction 3) has leakage family $\mathcal A(W)$ with leakage error at most $15\varepsilon$. Moreover, for every leakage family $W$ on a finite alphabet, if $W$ is affine-symmetric then so is $\mathcal A(W)$.
--
--   This is the privacy half of one RM step: the leakage of the amplified encoding is the induced family $\mathcal A(W)$, which the $\chi^2$ analysis of §6 then controls.
--
--   **Formalization Note.** "Has leakage family $W$" is `HasLeakage` with the leakage $L(x,y,z,w)=W_{(x,y,z)}$; leakage simulators use uniform coin bits.
--
--   Differences from the source:
--
--   - encoding: E a randomized encoding of f → Enc4: an encoder given by an F₂-polynomial description with a decoder; reason: every map between bit strings is a polynomial map over F₂
--   - encoding: E has leakage family W → HasLeakage with L(x, y, z, w) = W_{(x,y,z)}; reason: the leakage depends on the input through the secret s = (x, y, z)
--   - encoding: positions I = F₂⁴ ∖ {0} → Fin 15, position k the vector of binary digits of k + 1; reason: an enumeration of I; each nonzero vector occurs once
--   - encoding: distributions on a finite set → nonnegative functions Ω → ℝ of total mass one (IsLaw / IsLeakageFamily); reason: finite distributions as probability vectors
--   - encoding: A preserves affine symmetry → the second clause assumes IsLeakageFamily W; reason: A(W) is defined on p. 22 only for a leakage family W, so this is the page's standing context, not an added condition
-- source:
--   Applebaum, Quadratic Statistical Randomized Encoding for All Functions, STOC 2027 submission (manuscript sha256 000cbf4e…), p. 23, Proposition 4.4

import Mathlib
import Definitions.Def_QuadStatRE_Main_LeakyEncoding
import Definitions.Def_QuadStatRE_Main_LeakageFamily
import Definitions.Def_QuadStatRE_Main_RMSharing
open QuadraticRE

namespace QuadStatRE.Main

/-- Proposition 4.4 (Leaky simulation under amplification), p. 23: if `E` has leakage family
`W = (W_s)_{s ∈ G}` with leakage error `ε`, its amplification has leakage family `A(W)` with leakage
error at most `15ε`; moreover `A` preserves affine symmetry. -/
theorem proposition_4_4 :
    (∀ (E : Enc4) (Ω : Type) [Fintype Ω] (W : G → Ω → ℝ) (ε : ℝ),
      HasLeakage targetF E.desc.eval (fun v => W (secretOf v)) ε →
        HasLeakage targetF (amplify E).desc.eval (fun v => amp W (secretOf v)) (15 * ε)) ∧
    (∀ (Ω : Type) [Fintype Ω] (W : G → Ω → ℝ),
      IsLeakageFamily W → AffineSymmetric W → AffineSymmetric (amp W)) := by sorry

end QuadStatRE.Main
