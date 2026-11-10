-- Prove2me | Theorems.Thm_SymmetricPSM1041_ORLowerBound_protocol_induces_cube_system
-- name    : SymmetricPSM1041.ORLowerBound.protocol_induces_cube_system
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T12:57:44.576632+00:00
-- url     : https://prove2.me/theorems/f1c7d960-3dd9-47a0-9bbf-907f275a9564
-- title:
--   Lemma 12 — PSM induces an f-cube system
-- statement:
--   Let $f:\{0,1\}^n\to\{0,1\}$ be any Boolean function, and let $P$ be a perfectly correct, support-private PSM protocol with its declared message space $\Omega=\prod_i\mathcal M_i$. Let $\mathcal Q_P$ contain the ordered cube whose endpoints are $M_i(0,r),M_i(1,r)$ for each seed $r$, and let $Z_{P,b}$ contain exactly the transcripts occurring on inputs with output $b$. Then
--
--   $$\bigl(\mathcal Q_P,Z_{P,0},Z_{P,1}\bigr)\text{ is an }f\text{-cube system over }\Omega.$$
--
--   The statement supplies the canonical cube system from the source's proof, retaining the exact declared product alphabets. It applies to constant functions, irrelevant coordinates and zero parties as well as to OR. No relevance, endpoint distinctness or protocol symmetry is assumed.
--
--   Differences from the source:
--   - encoding: parties indexed by [n]={1,…,n} → parties indexed by Fin n; reason: the bijection i↦i+1 preserves every input and coordinate subset
--   - encoding: arbitrary finite nonempty shared seed set R → Fin P.seedCount with positive unrestricted seedCount; reason: reindexing preserves uniform laws, supports and realized lengths
--   - encoding: existence of an f-cube system → the source proof’s canonical cubes and output supports satisfy the axioms; reason: these are precisely the witnesses constructed on pp. 11–12
-- source:
--   Marshall Ball, Peter Crawford-Kahrl, Vladimir Podolskii, Morgan Prior, STOC 2027 submission #1041 (October 2026), p. 11, Lemma 12 (proof continues p. 12)

import Mathlib
import Definitions.Def_SymmetricPSM1041_ORLowerBound_CubeSystems

namespace SymmetricPSM1041.ORLowerBound

theorem protocol_induces_cube_system {n : ℕ} (f : (Fin n → Bool) → Bool)
    (P : PSM (Fin n)) (hc : PerfectCorrect P f) (hp : SupportPrivate P f) :
    IsCubeSystem f (protocolCubes P) (protocolOutputSupports P f) := by sorry

end SymmetricPSM1041.ORLowerBound
