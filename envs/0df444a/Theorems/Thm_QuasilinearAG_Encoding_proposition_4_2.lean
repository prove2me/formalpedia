-- Prove2me | Theorems.Thm_QuasilinearAG_Encoding_proposition_4_2
-- name    : QuasilinearAG.Encoding.proposition_4_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T15:41:56.003001+00:00
-- url     : https://prove2.me/theorems/b0164976-6b4d-4a7b-9105-4648833feaa1
-- title:
--   Proposition 4.2 — $U_h$, $U_h^{-1}$, $U_h^{\mathsf T}$, $U_h^{-\mathsf T}$ in $D\,\mathrm{poly}(q,h,Q_*)$ field operations and $O(D+(q+\kappa)Q_*+q^2)$ live slots
-- statement:
--   For arbitrary ambient $\kappa$ and $Q_*=q^\kappa$, the four maps $U_h$, $U_h^{-1}$, $U_h^{\mathsf T}$, $U_h^{-\mathsf T}$ have algorithms taking $D\,\mathrm{poly}(q,h,Q_*)$ field operations, with live field storage
--   $$O\big(D+(q+\kappa)Q_*+q^2\big).\qquad(4.12)$$
--   Precisely: there are absolute constants $c,C$ such that for every prime power $q>2$, the field $k=\mathbb F_{q^2}$, every $\theta$ with $\theta^q+\theta=1$ and every enumeration $\omega$ of $C=\ker(X^q+X)$ (which fix the path order (A1.2)), there are four programs of the algebraic RAM over $k$ such that for every height $h\ge1$, every $\kappa\ge0$, every good $\beta$ and every $v\in k^D$, $D=q^h$ (input: $h,\kappa$ in the index cells, $\beta,v$ in the field cells), the fibre matrix $U_h$ of (4.4) is invertible and the programs output $U_hv$, $U_h^{-1}v$, $U_h^{\mathsf T}v$, $U_h^{-\mathsf T}v$, each within $C\,D\,(q\,h\,Q_*)^c$ operations and $C\,(D+(q+\kappa)Q_*+q^2)$ slots at every step.
--
--   Differences from the source:
--   - generalization: D poly(q,h,Q*) field operations; live field storage O(D + (q+κ)Q* + q²) → every executed instruction (field and index) is counted; the slot bound covers the field cells and also the index cells and their bits; reason: the Lean measures are at least the field-operation count and the field-slot count, so the Lean bounds imply the printed ones
--   - reading: "the four maps … have algorithms" → one program per map, uniform in h, κ, β and v (it may depend on k, θ, ω), with poly(q,h,Q*) = C(q h Q*)^c and O(·) = C·(·) for absolute c, C; reason: the stronger reading; the algorithms of §4 receive h, κ and the path data as input
--   - encoding: U_h and the deterministic path order (A1.2) → fibreMatrix via the root levels (4.3) and (4.4), for every admissible θ and enumeration ω of C; IsUnit U_h as part of the conclusion; reason: the paper fixes some choice; the statement holds for each, and U_h^{-1} is asserted to exist
-- source:
--   Chao, Liu, Li, Ma, Wang, Quasilinear Encoding at the Quadratic Alphabet Scale via Short Cartier Bases, STOC 2027 submission (manuscript sha256 355c15dc…), p. 15, Proposition 4.2, (4.12) (PDF p. 17)

import Mathlib
import Definitions.Def_QuasilinearAG_Encoding_Tower
import Definitions.Def_QuasilinearAG_Encoding_AlgRAM
import Definitions.Def_QuasilinearAG_Encoding_Fibre

namespace QuasilinearAG.Encoding

/-- Proposition 4.2 (The inverse and inverse transpose), p. 15 (PDF 17). There are absolute
constants `c, C` such that for every prime power `q > 2`, the field `k = F_{q²}`, every choice of
`θ` (`θ^q + θ = 1`) and of the enumeration `ω` of `C = ker(X^q + X)` ordering the children
`θϕ(α) + ω(c)` (A1.2), there are four programs of the algebraic RAM over `k` which, for every
height `h ≥ 1`, every ambient extraction count `κ ≥ 0` (`Q* = q^κ`), every good `β` and every
vector `v ∈ k^D` (`D = q^h`, given as `β, v` in the field cells and `h, κ` in the index cells),
apply `U_h`, `U_h^{-1}`, `U_h^T` and `U_h^{-T}` to `v` (the fibre matrix of (4.4), which is
invertible), each within `C·D·(q h Q*)^c` operations and with live storage
`C·(D + (q + κ)Q* + q²)` (4.12) at every step. -/
theorem proposition_4_2 :
    ∃ (c : ℕ) (C : ℝ), 0 < C ∧
      ∀ (q : ℕ), IsPrimePow q → 2 < q →
      ∀ (k : Type) [Field k] [Fintype k], Fintype.card k = q ^ 2 →
      ∀ (θ : k) (ω : Fin q → k), θ ^ q + θ = 1 → Function.Injective ω →
        (∀ c, ω c ^ q + ω c = 0) →
      ∃ (Pfwd Pinv Ptr Pinvtr : AProgram k),
        ∀ (h κ : ℕ) (β : k), 1 ≤ h → IsGood q β →
          IsUnit (fibreMatrix q κ θ ω β h) ∧
          ∀ v : Fin (q ^ h) → k,
            AComputesVec Pfwd [h, κ] (β :: List.ofFn v) ((fibreMatrix q κ θ ω β h).mulVec v)
              (C * (q : ℝ) ^ h * ((q * h * q ^ κ : ℕ) : ℝ) ^ c)
              (C * ((q : ℝ) ^ h + ((q : ℝ) + κ) * (q : ℝ) ^ κ + (q : ℝ) ^ 2)) ∧
            AComputesVec Pinv [h, κ] (β :: List.ofFn v) ((fibreMatrix q κ θ ω β h)⁻¹.mulVec v)
              (C * (q : ℝ) ^ h * ((q * h * q ^ κ : ℕ) : ℝ) ^ c)
              (C * ((q : ℝ) ^ h + ((q : ℝ) + κ) * (q : ℝ) ^ κ + (q : ℝ) ^ 2)) ∧
            AComputesVec Ptr [h, κ] (β :: List.ofFn v)
              ((fibreMatrix q κ θ ω β h).transpose.mulVec v)
              (C * (q : ℝ) ^ h * ((q * h * q ^ κ : ℕ) : ℝ) ^ c)
              (C * ((q : ℝ) ^ h + ((q : ℝ) + κ) * (q : ℝ) ^ κ + (q : ℝ) ^ 2)) ∧
            AComputesVec Pinvtr [h, κ] (β :: List.ofFn v)
              ((fibreMatrix q κ θ ω β h)⁻¹.transpose.mulVec v)
              (C * (q : ℝ) ^ h * ((q * h * q ^ κ : ℕ) : ℝ) ^ c)
              (C * ((q : ℝ) ^ h + ((q : ℝ) + κ) * (q : ℝ) ^ κ + (q : ℝ) ^ 2)) := by sorry

end QuasilinearAG.Encoding
