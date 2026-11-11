-- Prove2me | Theorems.Thm_SAInterp_Res2_lemma_7_8
-- name    : SAInterp.Res2.lemma_7_8
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T22:41:52.020621+00:00
-- url     : https://prove2.me/theorems/209b30f5-e547-4dbb-906d-ea645e44528f
-- title:
--   Lemma 7.8 — under E_µ a bottom-row selector indicator [e_u = σ] can be exchanged for the colour indicator [c_{u,σ} = 1]
-- statement:
--   For all sufficiently large $n$, with $d=\lfloor n/100\rfloor$, the following holds. For every node $u\in\{n\}\times[n]$ on the bottom row, every colour $\sigma\in[n]$ and every indicator conjunction $C$ with $\mathrm{bdeg}(C)\le d-1$,
--   $$E_\mu\bigl[[\![e_u=\sigma]\!]\,C\bigr]=E_\mu\bigl[[\![c_{u,\sigma}=1]\!]\,C\bigr].$$
--   This exchange is used both to kill witnessing conjunctions (Lemma 7.1) and to remove bottom-row selectors before proving positivity (Lemma 7.2).
--
--   Differences from the source:
--   - reading: the standing assumption of §6 "Let n be sufficiently large" → ∃ N0, ∀ n ≥ N0; reason: explicit form of the standing assumption.
--   - reading: d = n/100 → d = ⌊n/100⌋; reason: µ needs an integer d.
--   - encoding: bdeg(C) ≤ d − 1 → bdeg C + 1 ≤ d; the product [[e_u = σ]]C → the conjunction C with the indicator inserted (the same element of A(X)); u ∈ {n} × [n] → row index n − 1 (0-based); reason: avoids ℕ subtraction; Lean conventions.
-- source:
--   Acheampong, Davis, Robere, Polynomial Interpolation for Sherali-Adams Lower Bounds, STOC 2027 submission (manuscript sha256 8de0a787…), p. 35 (PDF p. 37), Lemma 7.8

import Mathlib
import Definitions.Def_SAInterp_Res2_Indicator
import Definitions.Def_SAInterp_Res2_CPLS
import Definitions.Def_SAInterp_Res2_CPLSDist

namespace SAInterp.Res2

/-- Lemma 7.8 (p. 35), for all sufficiently large `n`, with `d = ⌊n/100⌋`: for any node `u` on
the bottom row, any colour `σ ∈ [n]` and any indicator conjunction `C` with
`bdeg(C) ≤ d − 1`, `E_µ[⟦e_u = σ⟧ C] = E_µ[⟦c_{u,σ} = 1⟧ C]`. -/
theorem lemma_7_8 :
    ∃ N0 : ℕ, ∀ n : ℕ, N0 ≤ n → ∀ (i j σ : Fin n), i.val + 1 = n →
      ∀ C : IndConj (cplsSize n), bdeg C + 1 ≤ cplsD n →
        Emu n (indConj (insert (indSel i j σ) C)) =
          Emu n (indConj (insert (indCol i j σ 1) C)) := by sorry

end SAInterp.Res2
