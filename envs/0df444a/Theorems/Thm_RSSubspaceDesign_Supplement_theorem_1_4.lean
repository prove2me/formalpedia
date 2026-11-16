-- Prove2me | Theorems.Thm_RSSubspaceDesign_Supplement_theorem_1_4
-- name    : RSSubspaceDesign.Supplement.theorem_1_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T20:38:05.01147+00:00
-- url     : https://prove2.me/theorems/574a071f-5b6b-4763-bda1-f7586a2ebba4
-- title:
--   Theorem 1.4 — explicit RS codes that are $(1-R-\varepsilon, O(t/\varepsilon+\varepsilon^{-3}), t)$-$F$-line-decodable for all $t \ge 1$
-- statement:
--   Fix $0 < R < 1$ and $0 < \varepsilon < 1$. For all sufficiently large $n$ and every finite field $K$ with $|K| \ge n$, there is an explicit construction, in time $|K|^{O_\varepsilon(1)}$, of an extension field $F$ with $[F:K] = O_\varepsilon(1)$ and distinct evaluation points $\alpha_1, \dots, \alpha_n \in F$ such that, for every integer $t \ge 1$, the code $\mathrm{RS}_F((\alpha_1, \dots, \alpha_n), \lfloor Rn \rfloor)$ is
--
--   $$
--   \Bigl(1 - R - \varepsilon,\ O\Bigl(\frac{t}{\varepsilon} + \varepsilon^{-3}\Bigr),\ t\Bigr)\text{-}F\text{-line-decodable}.
--   $$
--
--   So whenever $O(t/\varepsilon + \varepsilon^{-3})$ points $\alpha \in F$ of an affine line $u_0 + \alpha u_1$ over the extension field are within relative distance $1 - R - \varepsilon$ of assigned codewords, at least $t$ of those codewords lie on a single line of codewords. This is the source of the paper's proximity-gap and correlated-agreement bounds (Corollary 1.5).
--
--   **Formalization Note** The construction model is that of the base Theorem 1.1. One machine $M$ per $\varepsilon$ halts within $|K|^C$ steps and outputs $h$ with $\deg h \le D$ and the points. $M$, $C$ and $D$ depend on $\varepsilon$ only, the threshold $N$ also on $R$. The $O(t/\varepsilon + \varepsilon^{-3})$ is $\lceil c\,(t/\varepsilon + 1/\varepsilon^3)\rceil$ for one absolute constant $c$, the same for every $t$. Line decodability is curve decodability with $\ell = 1$.
--
--   Differences from the source:
--   - reading: RS((α₁, …, αₙ), Rn) → RS_F(α, ⌊Rn⌋); reason: the proof (Corollary 8.2, p.42) uses RS_F(A, ⌊Rn⌋)
--   - reading: explicit construction in time |K|^{O_ε(1)} with [F : K] = O_ε(1), for fixed R and ε → one machine M, exponent C and degree bound D chosen after ε and before R; the threshold N after R; reason: O_ε(1) says the exponent and degree depend on ε only; the construction (Theorem 1.1 with r depending on ε only, Corollary 8.2) does not use R; this is the stronger of the two readings
--   - encoding: O(t/ε + ε⁻³) for all t ≥ 1 → ⌈c(t/ε + 1/ε³)⌉ with one absolute c chosen first; reason: the O-constant is absolute; line decodability gets easier as the threshold grows, so a larger threshold is the content of the O
--   - encoding: a finite field K and a deterministic construction or algorithm with a running time → K = 𝔽_p[Y]/(f) input as p and a monic irreducible f; F = K[X]/(h) for a monic irreducible h; field elements by power-basis coordinates decoded structurally; one multi-stack Turing machine with an explicit step bound; reason: the base mission's published machine model; every finite field and every finite extension is isomorphic to one of these
-- source:
--   Alrabiah–Goyal–Guruswami, Explicit Reed-Solomon Subspace Designs: Optimal List and Line Decoding, arXiv:2610.36215 (held version, sha256 cf26424b…f36206), Theorem 1.4, p.6 (PDF 8); proved by Corollary 8.2, pp.42–43 (PDF 44–45)

import Mathlib
import Definitions.Def_Yukon_e9ee7c0e88307b8acac3260e
import Definitions.Def_HMBinPacking_OutputsWithin
import Definitions.Def_RSListDecodingCapacity_AllRates_Encoding
import Definitions.Def_RSSubspaceDesign_decPoly
import Definitions.Def_RSSubspaceDesign_IsCoeffList
import Definitions.Def_RSSubspaceDesign_encField
import Definitions.Def_RSSubspaceDesign_Supplement_IsCurveDecodable

open Polynomial RSListDecodingCapacity.AllRates

namespace RSSubspaceDesign

namespace Supplement

/-- **Theorem 1.4 (Explicit RS codes line-decodable up to capacity).** Alrabiah–Goyal–Guruswami,
arXiv:2610.36215 (held version, sha256 cf26424b…f36206), Theorem 1.4, p.6 (proved by Corollary 8.2,
pp.42–43).

Fix `0 < R < 1` and `0 < ε < 1`. For all sufficiently large `n` and every finite field `K` with
`|K| ≥ n`, there is an explicit construction of an extension field `F` with `[F : K] = O_ε(1)` along
with explicit evaluation points `α₁, …, αₙ ∈ F` in time `|K|^{O_ε(1)}` such that for all `t ≥ 1`,
`RS((α₁, …, αₙ), Rn)` is `(1 − R − ε, O(t/ε + ε⁻³), t)`-`F`-line-decodable.

**Formalization Note.** The machine model and encodings are those of the base mission's Theorem 1.1:
`K` is input as a prime `p` and a monic irreducible `f ∈ 𝔽_p[Y]` (`K = AdjoinRoot f`,
`|K| = p^{deg f}`), followed by `n`; the output is a monic irreducible `h ∈ K[X]` (`F = K[X]/(h)`,
`[F : K] = deg h`) and the `n` points in the power basis of `F/K`, decoded structurally
(`decPoly`, `AdjoinRoot.mk`); the points are distinct. "Explicit construction in time
`|K|^{O_ε(1)}`" is one machine `M` per `ε` halting within `|K|^C` steps, with `[F : K] ≤ D`; `M`, `C`,
`D` depend on `ε` only (as `O_ε(1)` says), the threshold `N` on `R` and `ε`. `O(t/ε + ε⁻³)` is
`⌈c(t/ε + 1/ε³)⌉` with one absolute constant `c` chosen first; curve decodability only gets easier
as the threshold `a` grows, so this is the content of the `O`. `Rn` is `⌊Rn⌋` (its proof,
Corollary 8.2, uses `RS_F(A, ⌊Rn⌋)`). `F`-line decodability is `IsCurveDecodable F · 1`. -/
theorem theorem_1_4 :
    ∃ c : ℕ, ∀ ε : ℝ, 0 < ε → ε < 1 →
      ∃ (M : Turing.TM2ComputableAux Bool Bool) (D C : ℕ),
        ∀ R : ℝ, 0 < R → R < 1 → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        ∀ (p : ℕ) [Fact p.Prime] (f : (ZMod p)[X]) [Fact (Irreducible f)], f.Monic →
          n ≤ p ^ f.natDegree →
          ∃ (hc : List (List ℕ)) (ac : List (List (List ℕ))),
            IsCoeffList p f ((decPoly p f hc).natDegree + 1) hc ∧
            ac.length = n ∧ (∀ x ∈ ac, IsCoeffList p f (decPoly p f hc).natDegree x) ∧
            HMBinPacking.OutputsWithin M (encField p f ++ encNat n)
              (encList (encList encNat) hc ++ encList (encList (encList encNat)) ac)
              ((p ^ f.natDegree) ^ C) ∧
            (decPoly p f hc).Monic ∧ (decPoly p f hc).natDegree ≤ D ∧
            ∃ hirr : Irreducible (decPoly p f hc),
            haveI : Fact (Irreducible (decPoly p f hc)) := ⟨hirr⟩
            ∃ hα : Function.Injective fun i : Fin n =>
                AdjoinRoot.mk (decPoly p f hc) (decPoly p f (ac.getD i [])),
              ∀ t : ℕ, 1 ≤ t →
                IsCurveDecodable (AdjoinRoot (decPoly p f hc))
                  (ReedSolomon.code ⟨_, hα⟩ ⌊R * n⌋₊) 1 (1 - R - ε)
                  ⌈(c : ℝ) * ((t : ℝ) / ε + 1 / ε ^ 3)⌉₊ t := by sorry

end Supplement

end RSSubspaceDesign
