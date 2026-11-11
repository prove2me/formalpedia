-- Prove2me | Theorems.Thm_PolySwap_KMS_theorem_1_2
-- name    : PolySwap.KMS.theorem_1_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T02:38:55.172703+00:00
-- url     : https://prove2.me/theorems/198b29ac-4499-4c62-9a0e-ee3cbe87cc4c
-- title:
--   Theorem 1.2 (Main) — congruence KMS complexes $X(A_d,\mathbb F_q,f)$ are $(r,\Omega(r^{-34}),m)$-swap coboundary expanders; bounded-degree families exist
-- statement:
--   There are absolute constants $c>0$ and $C\ge1$ such that for every $r\ge1$, every prime power $q\ge C\,r^C$ and every $d\ge C\,r^C$ (so $q_0,d_0=\mathrm{poly}(r)$ and $\Omega(r^{-34})=c\,r^{-34}$):
--
--   1. for every irreducible $f\in\mathbb F_q[t]$ of degree $\ge2$, the congruence KMS complex $X=X(A_d,\mathbb F_q,f)$ is an $(r,c\,r^{-34},m)$-swap coboundary expander for every integer $1\le m<\mathrm{char}(\mathbb F_q)$; that is, its $r$-faces complex $F^rX$ is a $(c\,r^{-34},m)$-coboundary expander: for every antisymmetric $f:\vec{F^rX}(1)\to\mathrm{Sym}_m$ there is $g:F^rX(0)\to\mathrm{Sym}_m$ with
--   $$c\,r^{-34}\cdot\Pr_{uv}\big[f(uv)\ne g(v)g(u)^{-1}\big]\le\Pr_{uvw}\big[f(uv)f(wu)f(vw)\ne\mathrm{Id}\big],$$
--   probabilities with respect to the natural (Garland) distribution of $F^rX$;
--   2. if moreover $q>d^2$, there is a sequence of such $d$-dimensional complexes $X(A_d,\mathbb F_q,f_k)$ ($f_k$ irreducible of degree $\ge2$) whose number of vertices tends to infinity, whose vertex degrees are at most $\exp(C\,d^2\log q)$, and each of which is simultaneously a $\frac1{\sqrt q-(d-1)}$-local spectral expander and an $(r,c\,r^{-34},m)$-swap coboundary expander for every integer $1\le m<\mathrm{char}(\mathbb F_q)$.
--
--   The body version is Corollary 3.2 (p. 21), with the parameters of Theorem 3.1.
--
--   Differences from the source:
--   - encoding: Ω(r⁻³⁴), q₀, d₀ = poly(r) and exp(O(d² log q)), for every r → ∃ c > 0 and ∃ C ≥ 1 (natural) before r, F, d, f, m: β = c/r³⁴, q ≥ C·r^C, d ≥ C·r^C, degree ≤ exp(C·d²·log q); r ≥ 1; reason: the uniform reading with absolute constants; any polynomial threshold is dominated by C·r^C; the paper's ℕ excludes 0 (p. 9)
--   - encoding: a prime power q = p^m and the field F_q → a finite field F (Fintype F) with q = Fintype.card F and p = ringChar F; reason: every finite field has prime-power order q and prime characteristic p; same instances
--   - encoding: X(A_d, F_q, f) = CC(SL_{d+1}(F_q[t]/(f)); (π_f(U_{[d]∖{i}}))_{i∈[d]}) with the uniform distribution → the published LowAccLTC.kmsComplex (d + 1) f, whose subgroups are given entrywise as (T₁ 0; tS T₂) with T₁, T₂ upper unitriangular over F_q (colour i of the definition = colour i of the paper); reason: the two descriptions coincide ([GV25, Lemmas 4.2, 4.6], cited p. 27): products of the generators never create t², and π_f is injective on these groups for deg f ≥ 2
--   - encoding: (r, β, m)-swap coboundary expander (Definition 1.1, (1.1)): F^rX, r-faces with r + 1 vertices, Sym_m, the natural distribution → IsFacesCoboundaryExpander (r + 1) m β of the published definition: j = r + 1 counts vertices; Sym_m = Equiv.Perm (Fin m); edges and triangles of F^rX sampled from a uniform top face and a uniform ordered pair/triple of disjoint (r+1)-colour sets; the triangle event ϕ(wu)ϕ(vw)ϕ(uv) ≠ 1; reason: the same measure (Definition 2.11); ϕ(wu)ϕ(vw)ϕ(uv) is a cyclic conjugate of f(uv)f(wu)f(vw), so the events coincide
--   - encoding: the field F_q[t]/(f) as a finite type → the Fintype and DecidableEq instances on AdjoinRoot f universally quantified; reason: such instances exist (f ≠ 0, F finite) and all of them are equal
--   - generalization: there exists a sequence of d-dimensional complexes with these properties → the sequence is X(A_d, F_q, f_k) = kmsComplex (d + 1) (f_k) for irreducible f_k of degree ≥ 2; reason: naming the witness family is stronger and implies the printed existential
--   - encoding: vertex degree deg(v) = |{τ ∈ X(d) : v ∈ τ}|; 1/(√q − (d − 1))-local spectral expander (Definition 2.7) → card of star {v} for every v ∈ vertices; IsOneSidedLocalSpectral (variational form of λ₂ ≤ ε on every link X_s with |s| ≤ d − 1); reason: the published definitions; equivalent
-- source:
--   Dikstein, Oppenheim, Valentiner-Branth, Polynomial Swap Coboundary Expansion with Applications to LTCs and PCPs, STOC 2027 submission (manuscript sha256 b9cb2095…), Theorem 1.2, p. 2 (body: Corollary 3.2 with Theorem 3.1, p. 21; spectral clause from Theorem 2.19, p. 16)

import Mathlib
import Definitions.Def_LowAccLTC_kmsComplex
import Definitions.Def_LowAccLTC_IsFacesCoboundaryExpander
import Definitions.Def_LowAccLTC_IsOneSidedLocalSpectral

open Polynomial Filter

universe u

namespace PolySwap.KMS

/-- **Theorem 1.2** (Main), p. 2. There are absolute constants `c > 0` and `C ≥ 1` (so that
`Ω(r⁻³⁴) = c·r⁻³⁴` and `q₀ = d₀ = C·r^C = poly(r)`) such that for every `r ≥ 1`, every finite
field `F_q` with `q ≥ C·r^C` and every `d ≥ C·r^C`:
* for every irreducible `f ∈ F_q[t]` of degree `≥ 2`, the congruence KMS complex
  `X = X(A_d, F_q, f)` is an `(r, c·r⁻³⁴, m)`-swap coboundary expander for every integer
  `1 ≤ m < char F_q`: its `r`-faces complex `F^r X` (faces with `r + 1` vertices, so `j = r + 1`)
  satisfies (1.1) with `Sym_m` coefficients and the natural weights;
* if moreover `q > d²`, there is a sequence of such `d`-dimensional complexes
  `X(A_d, F_q, f_k)` whose number of vertices tends to infinity, whose vertex degrees are at most
  `exp(C d² log q)`, and each of which is a `1/(√q − (d − 1))`-local spectral expander and an
  `(r, c·r⁻³⁴, m)`-swap coboundary expander for every integer `1 ≤ m < char F_q`. -/
theorem theorem_1_2 : ∃ c : ℝ, 0 < c ∧ ∃ C : ℕ, 1 ≤ C ∧
    ∀ r : ℕ, 1 ≤ r → ∀ (F : Type u) [Field F] [Fintype F], C * r ^ C ≤ Fintype.card F →
    ∀ d : ℕ, C * r ^ C ≤ d →
      (∀ f : F[X], Irreducible f → 2 ≤ f.natDegree →
        ∀ [Fintype (AdjoinRoot f)] [DecidableEq (AdjoinRoot f)],
        ∀ m : ℕ, 1 ≤ m → m < ringChar F →
          (LowAccLTC.kmsComplex (d + 1) f).IsFacesCoboundaryExpander (r + 1) m
            (c / (r : ℝ) ^ 34)) ∧
      (d ^ 2 < Fintype.card F →
        ∃ fs : ℕ → F[X], (∀ k, Irreducible (fs k) ∧ 2 ≤ (fs k).natDegree) ∧
          ∀ (inst : ∀ k, Fintype (AdjoinRoot (fs k)))
            (dec : ∀ k, DecidableEq (AdjoinRoot (fs k))),
            Tendsto (fun k => (@LowAccLTC.kmsComplex F _ (d + 1) (fs k) (inst k) (dec k)).vertices.card)
              atTop atTop ∧
            ∀ k,
              (∀ v ∈ (@LowAccLTC.kmsComplex F _ (d + 1) (fs k) (inst k) (dec k)).vertices,
                (((@LowAccLTC.kmsComplex F _ (d + 1) (fs k) (inst k) (dec k)).star {v}).card : ℝ) ≤
                  Real.exp (C * (d : ℝ) ^ 2 * Real.log (Fintype.card F))) ∧
              (@LowAccLTC.kmsComplex F _ (d + 1) (fs k) (inst k) (dec k)).IsOneSidedLocalSpectral
                (1 / (Real.sqrt (Fintype.card F) - ((d : ℝ) - 1))) ∧
              ∀ m : ℕ, 1 ≤ m → m < ringChar F →
                (@LowAccLTC.kmsComplex F _ (d + 1) (fs k) (inst k) (dec k)).IsFacesCoboundaryExpander
                  (r + 1) m (c / (r : ℝ) ^ 34)) := by sorry

end PolySwap.KMS
