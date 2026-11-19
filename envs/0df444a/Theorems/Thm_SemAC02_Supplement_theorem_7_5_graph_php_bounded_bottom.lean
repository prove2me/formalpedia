-- Prove2me | Theorems.Thm_SemAC02_Supplement_theorem_7_5_graph_php_bounded_bottom
-- name    : SemAC02.Supplement.theorem_7_5_graph_php_bounded_bottom
-- status  : Proved
-- author  : @iris
-- created : 2026-11-15T19:53:27.920902+00:00
-- url     : https://prove2.me/theorems/56675c27-2cfd-49ca-ab56-f559b320c3ee
-- title:
--   Theorem 7.5 — graph PHP needs semantic ΣΠΣΠ[w]-PC size (1/4)exp(c₀n/(wΔ(C₀Δ²)^w))
-- statement:
--   There are absolute constants $c_0,C_0>0$ such that for all sufficiently large $n$ the following holds. Let $G$ satisfy the conclusions of Lemma 7.4 (with $\Delta=\lceil24\ln(2n)\rceil$). Simultaneously for every integer $1\le w\le\ln n/\ln\ln n$, every arity-2 semantic ΣΠΣΠ[$w$]-PC refutation $\pi$ of $\mathrm{PHP}(G)$ over $\mathbb F_2$ satisfies
--
--   $$
--   S(\pi)\ \ge\ \frac14\exp\Bigl(\frac{c_0n}{w\Delta(C_0\Delta^2)^w}\Bigr).
--   $$
--
--   The same lower bound holds for the more general refutations whose semantic inferences need only be sound on the hole domain $\Omega_{F_0}=\{\alpha\in\{0,1\}^{nD}:f(\alpha)=0\ \forall f\in F_0\}$ and whose initial lines need only agree on $\Omega_{F_0}$ with an axiom of $\mathrm{PHP}'(G)$ or with $0$; $S(\pi)$ then counts classes in $B_{F_0}$.
--
--   This is the bounded-bottom-fan-in step of the lower bound for the complete PHP (Theorem 7.14).
--
--   **Formalization Note** $D=4\Delta$. In the general form the variables are $(v,j)$, $j\in[D]$, with the edge variables of hole $v$ placed by an arbitrary injection; $\Omega_{F_0}$ is the set of points with at most one $1$ per class.
--
--   Differences from the source:
--   - encoding: proof lines are displayed circuits representing classes in B_n; initial lines are the axioms → ACirc terms; a line is an axiom line when its value on the cube equals an axiom; initial lines equal to 0 are allowed; reason: p.15: a line represents its residue class; p.54: initial tautologies 0 = 0; a zero line follows from any line, so no refutation or measure changes
--   - encoding: padding each hole class with auxiliary variables to size D → variables Fin n × Fin D, edge variables placed by any injection ι, statement for every ι; reason: the padding is arbitrary and every choice is covered
--   - encoding: absolute c₀, C₀ and sufficiently large n → ∃ c₀ C₀ > 0, ∃ n₀, ∀ n ≥ n₀; reason: asymptotic notation as explicit quantifiers
-- source:
--   Alekseev, Gryaznov, Itsykson, Pitassi, Robere, Tzameret, Hard Instances for Strong Semantic Proof Systems: CNFs for Depth-Four PC and Deep Instances for AC0[2]-Frege, manuscript (STOC 2027 submission, sha256 c228d68b89b45b5c6c547aa994f7d1799441bb22b2a85e36c6cd400bea8cdb6a), Theorem 7.5, p.53 (PDF p.55); Lemma 7.4 and (29), p.52 (PDF p.54)

import Mathlib
import Definitions.Def_PCNonBool_BipGraph
import Definitions.Def_SemAC02_nDivision
import Definitions.Def_SemAC02_Supplement_ACirc
import Definitions.Def_SemAC02_Supplement_IsSemPCRef
import Definitions.Def_SemAC02_Supplement_fphpG
import Definitions.Def_SemAC02_Supplement_phpG

namespace SemAC02.Supplement

open ACirc

/-- **Theorem 7.5 (Bounded-bottom-degree graph PHP)** (Alekseev–Gryaznov–Itsykson–Pitassi–Robere–
Tzameret, *Hard Instances for Strong Semantic Proof Systems*, manuscript (STOC 2027 submission),
Theorem 7.5, p.53): there are absolute constants `c₀, C₀ > 0` such that the following holds for
all sufficiently large `n`. Let `G` satisfy the conclusions of Lemma 7.4. Simultaneously for every
integer `1 ≤ w ≤ ln n / ln ln n`, every semantic ΣΠΣΠ[w]-PC refutation `π` of `PHP(G)` satisfies
`S(π) ≥ (1/4) exp(c₀n/(wΔ(C₀Δ²)^w))`. The same lower bound holds for the following more general
form of a semantic refutation: semantic inferences need only be sound on the hole domain
`Ω_{F₀} = {α ∈ {0,1}^{nD} : f(α) = 0 for every f ∈ F₀}`, and every initial line need only agree on
`Ω_{F₀}` either with an axiom of `PHP′(G)` or with the zero polynomial.

**Formalization Note** `Δ = ⌈24 ln(2n)⌉` and `D = 4Δ` (Lemma 7.4 and p.52). `c₀`, `C₀`, `n₀` are
absolute. `PHP(G)` is over `𝔽₂`. In the general form the variables are `Fin n × Fin D` (the class
`C_v = {v} × [D]` of hole `v`), the edge variables being placed by an arbitrary injection `ι`, so
`Ω_{F₀} = nDivOmega n D`; `S(π)` then counts classes in `B_{F₀}` (functions on `Ω_{F₀}`). Initial
lines equal to zero on `Ω_{F₀}` are allowed by `IsSemPCRef`. -/
theorem theorem_7_5_graph_php_bounded_bottom :
    ∃ c₀ C₀ : ℝ, 0 < c₀ ∧ 0 < C₀ ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ∀ G : PCNonBool.BipGraph (Fin (2 * n)) (Fin n), Lemma74Concl G →
      ∀ w : ℕ, 1 ≤ w → (w : ℝ) ≤ Real.log n / Real.log (Real.log n) →
        (∀ π : List (ACirc (ZMod 2) (Edge G)),
          IsSemPCRef (IsSPSP (w : ℕ∞)) Set.univ (polyAx (phpG G)) π →
          1 / 4 * Real.exp (c₀ * n / (w * php74Delta n *
            (C₀ * (php74Delta n : ℝ) ^ 2) ^ w)) ≤ topS Set.univ π) ∧
        (∀ (ι : ∀ v : Fin n, {u : Fin (2 * n) // G.Adj u v} ↪ Fin (4 * php74Delta n))
          (π : List (ACirc (ZMod 2) (Fin n × Fin (4 * php74Delta n)))),
          IsSemPCRef (IsSPSP (w : ℕ∞)) (nDivOmega n (4 * php74Delta n))
            (polyAx (phpPadded G ι)) π →
          1 / 4 * Real.exp (c₀ * n / (w * php74Delta n *
            (C₀ * (php74Delta n : ℝ) ^ 2) ^ w)) ≤ topS (nDivOmega n (4 * php74Delta n)) π) := by sorry

end SemAC02.Supplement
