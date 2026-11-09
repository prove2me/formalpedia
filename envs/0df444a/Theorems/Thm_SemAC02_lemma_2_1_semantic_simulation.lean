-- Prove2me | Theorems.Thm_SemAC02_lemma_2_1_semantic_simulation
-- name    : SemAC02.lemma_2_1_semantic_simulation
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T11:26:57.683282+00:00
-- url     : https://prove2.me/theorems/66f41598-ceb5-436f-bffe-666112914f33
-- title:
--   Lemma 2.1 — PC simulates binary semantic PC with a factor $3$ in degree
-- statement:
--   Let $f_1,f_2,g\in\mathcal B_n(\mathbb F_2)$ have degree at most $d$, and suppose that $f_1(x)=f_2(x)=0$ implies $g(x)=0$ for every $x\in\mathbb F_2^n$. Then there are multilinear $h_1,h_2\in\mathcal B_n(\mathbb F_2)$ of degree at most $2d$ with
--   $$
--   g\equiv h_1f_1+h_2f_2 .
--   $$
--   Consequently $g$ has a syntactic PC derivation from $f_1$ and $f_2$ of degree at most $3d$.
--
--   Applied to every inference, the lemma turns a degree-$d$ semantic PC derivation into a syntactic one of degree $3d$.
--
--   Differences from the source:
--   - encoding: elements of B_n, their degree and products → multilinear MvPolynomial representatives, totalDegree, products ML(f·p) (mulML); reason: every element of B_n has a unique multilinear representative (p.15); same instances
--   - encoding: PC derivation in B_n; "a derivation of g" → PCNonBool.IsDerivation with reduction AC02Frege.ML; g occurs as a line; reason: lines are the multilinear representatives; the extra axiom multiple 0·a only adds zero lines, which can be deleted without changing any other line or degree
-- source:
--   Alekseev, Gryaznov, Itsykson, Pitassi, Robere, Tzameret, Hard Instances for Strong Semantic Proof Systems: CNFs for Depth-Four PC and Deep Instances for AC0[2]-Frege, manuscript (STOC 2027 submission, sha256 c228d68b89b45b5c6c547aa994f7d1799441bb22b2a85e36c6cd400bea8cdb6a), Lemma 2.1, p.17 (PDF p.19)

import Mathlib
import Definitions.Def_PCNonBool_IsDerivation
import Definitions.Def_AC02Frege_ML

namespace SemAC02

open MvPolynomial

/-- **Lemma 2.1 (PC simulates semantic PC with only a factor of three increase in degree)**
(Alekseev–Gryaznov–Itsykson–Pitassi–Robere–Tzameret, *Hard Instances for Strong Semantic Proof
Systems*, manuscript (STOC 2027 submission), Lemma 2.1, p.17): let `f₁, f₂, g ∈ B_n(𝔽₂)` have degree at most `d`, and suppose
that `f₁(x) = f₂(x) = 0` implies `g(x) = 0` for every `x ∈ 𝔽₂^n`. Then there are multilinear
polynomials `h₁, h₂ ∈ B_n(𝔽₂)` of degree at most `2d` such that `g ≡ h₁f₁ + h₂f₂`.
Consequently, `g` has a syntactic PC derivation from `f₁` and `f₂` of degree at most `3d`.

**Formalization Note** Elements of `B_n` are their multilinear representatives; degree is total
degree. `≡` is equality in `B_n`, i.e. of multilinear representatives: `g = ML(h₁f₁ + h₂f₂)`. The
PC derivation is the published `PCNonBool.IsDerivation` with reduction `AC02Frege.ML` (lines in
`B_n`) from the axioms `{f₁, f₂}`, containing `g`, with every line of degree at most `3d`. -/
theorem lemma_2_1_semantic_simulation {n : ℕ} (d : ℕ) (f₁ f₂ g : MvPolynomial (Fin n) (ZMod 2))
    (hf₁ : AC02Frege.IsMultilinear f₁) (hf₂ : AC02Frege.IsMultilinear f₂)
    (hg : AC02Frege.IsMultilinear g) (hd₁ : f₁.totalDegree ≤ d) (hd₂ : f₂.totalDegree ≤ d)
    (hdg : g.totalDegree ≤ d)
    (hsem : ∀ x : Fin n → ZMod 2, eval x f₁ = 0 → eval x f₂ = 0 → eval x g = 0) :
    (∃ h₁ h₂ : MvPolynomial (Fin n) (ZMod 2), AC02Frege.IsMultilinear h₁ ∧
        AC02Frege.IsMultilinear h₂ ∧ h₁.totalDegree ≤ 2 * d ∧ h₂.totalDegree ≤ 2 * d ∧
        g = AC02Frege.ML (h₁ * f₁ + h₂ * f₂)) ∧
    ∃ π : List (MvPolynomial (Fin n) (ZMod 2)),
      PCNonBool.IsDerivation AC02Frege.ML {f₁, f₂} π ∧ g ∈ π ∧
        ∀ p ∈ π, p.totalDegree ≤ 3 * d := by sorry

end SemAC02
