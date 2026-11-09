-- Prove2me | Theorems.Thm_RestrictedDec_timing_inclusions
-- name    : RestrictedDec.timing_inclusions
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T12:55:49.760679+00:00
-- url     : https://prove2.me/theorems/674fcaa8-47d1-4fc1-ba32-32ae0d30f47c
-- title:
--   §3.2 — $\mathrm{Sec}^{ad}(\mathcal F)\subseteq\mathrm{Sec}^{na}(\mathcal F)\subseteq\text{IND-CPA}$
-- statement:
--   For every family $\mathcal F$ of permitted functions and every scheme $\Pi$ over $\{0,1\}^{n(\lambda)}$:
--
--   $$\Pi\in\mathrm{Sec}^{ad}(\mathcal F)\ \Rightarrow\ \Pi\in\mathrm{Sec}^{na}(\mathcal F)\ \Rightarrow\ \Pi\text{ is IND-CPA secure}.$$
--
--   For a fixed collection of functions, allowing queries after the challenge can only help the adversary, and pre-challenge queries can only help against a CPA game. In the proof of Corollary 2 the first inclusion for $\mathcal F_{\mathrm{id}}$ turns the assumed IND-CCA2 scheme into the IND-CCA1 scheme the reverse construction starts from.
--
--   Differences from the source:
--   - reading: every PPT adversary → every uniform reactive machine with a polynomial-time step function and polynomial bounds on coins, state, moves and activations; reason: the paper's adversaries are uniform (p.15 'a single PPT attack', p.28 'a uniform adversary')
--   - encoding: the CPA experiment has no oracle → CPA query moves get no answer; reason: a refused query reveals nothing; same advantages
-- source:
--   Nguyen–Susilo, Between CPA and CCA: Security Hierarchies for Restricted Decryption, STOC 2027 submission (manuscript sha256 6aeac40c…), §3.2, p.16

import Mathlib
import Definitions.Def_RestrictedDec_Sec
import Definitions.Def_RestrictedDec_INDCPA
open QAlgorithms.Complexity
set_option autoImplicit false

namespace RestrictedDec

/-- **Timing inclusions** `Sec^ad(𝓕) ⊆ Sec^na(𝓕) ⊆ IND-CPA` (§3.2, p.16), for every family `𝓕`
of permitted functions and every scheme over `{0,1}^{n(λ)}`.
Nguyen–Susilo, STOC 2027 submission (manuscript sha256 6aeac40c…), §3.2, p.16 ("For a fixed
collection of functions, the definitions immediately give Secad(F) ⊆ Secna(F) ⊆ IND-CPA."). -/
theorem timing_inclusions (n : ℕ → ℕ) (F : Family) (P : PKE) :
    (Sec .ad n F P → Sec .na n F P) ∧ (Sec .na n F P → INDCPA n P) := by sorry

end RestrictedDec
